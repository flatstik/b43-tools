"""The corerev 40+ crypto engine for reception (CCMP), as the RT-AC56U's
BCM4352 shows it under 784.2's ucode42 (opt-in: RxEngine.crypto, rxframe.py
--crypto). Built from observables only: register writes and read-backs on the
chip (full MMIO matrices around WEP_CTL 0x0155), what reaches the host, and
802.11's CCMP itself.

The ucode programs it so for a frame whose transmitter has a key (condition
0x62):

  SPR 0x1E2   written twice: the MAC header's length, then the CCMP header's
              place (header length + 6; 0x1A / 0x20 for QoS data). 784.2
              writes the pair for every frame once its header is in.
  SPR 0x1E3   the MPDU's length (written at the frame's start).
  WEP_CTL     (SPR 0x1E0) the key's index / algorithm word from b43-next's key
              index block ((slot << 4) | algorithm, 5 AES), then
  SPR 0x1E4   0x0100, and the key's 8 words into
  SPR 0x1E5   (16 bytes, little-endian words), then
  WEP_CTL     that word | 0x0110: the start (0x0155 for slot 4).
  SPR 0x262   8 after the start (4 after the address lookup before it).

What the chip shows of it:

  - WEP_CTL reads back without bit 8 right after the start (0x0155 -> 0x0055)
    and gains bit 7 when the engine is done (0x00D5); 0x0150, the RX mode
    without a key, reads 0x0050.
  - A start with no key loaded latches bit 15 (0x8055, then 0x8010 after the
    next writes); it stays set through later writes and starts, which do
    nothing more, until the core is reset (a firmware reload).
  - SPR 0x1E1 steps while the frame passes (0x0003 at the start, 0x0A0B at
    the end, 0x040B / 0x080B / 0x0A0B / 0x400B / 0x4A0B in between); here
    only the first and last.
  - WEP_CTL 0x0075 then 0 (784.2's drop) resets the engine.
  - The frame reaches the host decrypted in place: the CCMP header kept, the
    plaintext from right after it, the MIC and FCS behind it as received.

Not known, so a choice (pad_rule): how the engine accounts for the RXE's
2-byte pad of a QoS frame. Under 784.2 the decryption lines up; under other
ucode42 builds on the chip it comes out 2 bytes early in some sessions and
right in others, with the same writes. "start" (the default) counts the pad
when FIFOCTL1 bit 5 was set before the start, "always" and "never" fix it.
"start" fits 784.2 (pad request at 37 us, start at 48 us) but not the chip
under other builds: one with the request after the start decrypted right in
its first sessions (the rule says early), one with it before came out early
(the rule says right), and both changed state within sessions.
Nor modelled: the MIC check's outcome (no RX status bit for it has been seen),
TKIP and WEP, the transmit side (WEP_CTL 0x0040 / 0x0010, 0x1F0-0x1F4)."""
import os

SPR_WEP_CTL, SPR_CRYPT_PROG, SPR_CRYPT_OFF, SPR_CRYPT_LEN = 0x1E0, 0x1E1, 0x1E2, 0x1E3
SPR_CRYPT_KCTL, SPR_CRYPT_KEY = 0x1E4, 0x1E5
WATCHED = (SPR_WEP_CTL, SPR_CRYPT_OFF, SPR_CRYPT_KCTL, SPR_CRYPT_KEY)
WEP_START, WEP_DONE, WEP_FAULT, WEP_ARMED = 0x0110, 0x0080, 0x8000, 0x0100
ALG_AES = 5
PROG_START, PROG_END = 0x0003, 0x0A0B
FIFOCTL1_PAD = 0x0020


def _aes_ecb(key):
    """An AES-128 block encryptor, or None without the cryptography package."""
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    except ImportError:
        return None
    enc = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return lambda block: enc.update(block)


def ccmp_nonce(mac):
    """CCMP's 13-byte nonce of an MPDU (802.11-2016 12.5.3.3.4): priority,
    A2, PN5..PN0."""
    fc = mac[0] | mac[1] << 8
    hl = 24 + (2 if fc & 0x0080 and (fc >> 2) & 3 == 2 else 0) + (6 if fc & 0x0300 == 0x0300 else 0)
    prio = mac[hl - 2] & 0x0F if fc & 0x0080 and (fc >> 2) & 3 == 2 else 0
    h = mac[hl:hl + 8]
    pn = bytes((h[7], h[6], h[5], h[4], h[1], h[0]))
    return bytes((prio,)) + mac[10:16] + pn, hl


class CryptoEngine:
    def __init__(self, chip, pad_rule=None):
        self.chip = chip
        self.pad_rule = pad_rule or os.environ.get("VCHIP_CRYPTO_PAD", "start")
        self.key_words = []
        self.loading = False
        self.offsets = []           # the last two SPR 0x1E2 writes
        self.fault = False          # bit 15, latched
        self.active = None          # (key, header length, CCMP header place, pad counted) of a started frame
        self.log = []               # (clock, event)

    # ---- the ucode's writes ----
    def written(self, n, old, new):
        c = self.chip
        if n == SPR_CRYPT_KCTL and new & 0x0100:
            self.key_words, self.loading = [], True
        elif n == SPR_CRYPT_KEY and self.loading:
            self.key_words.append(new & 0xFFFF)
            if len(self.key_words) == 8:
                self.loading = False
        elif n == SPR_CRYPT_OFF:
            self.offsets = (self.offsets + [new & 0xFFFF])[-2:]
        elif n == SPR_WEP_CTL:
            if new in (0x0075, 0x0000) and old == 0x0075:
                self.active = None
            if new & WEP_START == WEP_START and new & 0x000F == ALG_AES:
                self.start(new)
            value = new & ~WEP_ARMED
            if self.fault:
                value |= WEP_FAULT
            if value != new:
                c.m.spr[SPR_WEP_CTL] = value

    def start(self, value):
        c = self.chip
        if self.fault or len(self.key_words) < 8:
            self.fault = True
            self.active = None
            self.log.append((c.clock, "start without a key: bit 15 latched"))
            return
        key = b"".join(w.to_bytes(2, "little") for w in self.key_words)
        hdr_len, ccmp_at = (self.offsets + [0, 0])[:2] if len(self.offsets) == 2 else (0, 0)
        padded = bool(c.m.spr.get(0x004, 0) & FIFOCTL1_PAD)
        counted = {"always": True, "never": False}.get(self.pad_rule, padded)
        self.active = (key, hdr_len, ccmp_at, counted)
        c.m.spr[SPR_CRYPT_PROG] = PROG_START
        self.log.append((c.clock, f"start, offsets {hdr_len:#x} / {ccmp_at:#x}, pad {'counted' if counted else 'not counted'}"))

    # ---- the frame ----
    def deliver(self, data, pad):
        """The frame's bytes as the push hands them to the host: decrypted in
        place if the engine was started on it. data is the PLCP and the
        MPDU; pad, whether the RXE put 2 bytes before them."""
        c = self.chip
        if self.active is None:
            return data
        key, hdr_len, ccmp_at, counted = self.active
        self.active = None
        c.m.spr[SPR_CRYPT_PROG] = PROG_END
        c.m.spr[SPR_WEP_CTL] = c.m.spr.get(SPR_WEP_CTL, 0) | WEP_DONE
        aes = _aes_ecb(key)
        if aes is None:
            self.log.append((c.clock, "no AES (python3-cryptography): frame left as received"))
            return data
        buf = (b"\0\0" if pad else b"") + data
        # The CCMP header where the engine takes it: SPR 0x1E2's second value
        # counts from after the pad when the engine counts the pad; without
        # it the engine works 2 bytes early in a padded buffer.
        at = ccmp_at + (2 if pad and counted else 0)
        mac = buf[at - hdr_len:]
        nonce, _ = ccmp_nonce(bytes(mac[:hdr_len]) + bytes(buf[at:at + 8]))
        start, end = at + 8, len(buf) - 8 - 4       # the MIC and the FCS stay
        out = bytearray(buf)
        for i, off in enumerate(range(start, max(start, end), 16)):
            ks = aes(bytes((0x01,)) + nonce + (i + 1).to_bytes(2, "big"))
            for j in range(min(16, end - off)):
                out[off + j] ^= ks[j]
        self.log.append((c.clock, f"decrypted {max(0, end - start)} bytes from buffer offset {start}"))
        return bytes(out[2:] if pad else out)


def ccmp_encrypt(key, mac_plain, pn):
    """An MPDU (no FCS) of plaintext body made CCMP: the header's protected
    bit set, the CCMP header (key ID 0) after it, the body encrypted, the
    8-byte MIC appended (802.11-2016 12.5.3). For tests."""
    from cryptography.hazmat.primitives.ciphers.aead import AESCCM
    fc = mac_plain[0] | mac_plain[1] << 8 | 0x4000
    qos = fc & 0x0080 and (fc >> 2) & 3 == 2
    hl = 24 + (2 if qos else 0) + (6 if fc & 0x0300 == 0x0300 else 0)
    hdr = bytearray(mac_plain[:hl]); hdr[0], hdr[1] = fc & 0xFF, fc >> 8
    p = pn.to_bytes(6, "little")
    ccmp = bytes((p[0], p[1], 0, 0x20, p[2], p[3], p[4], p[5]))
    nonce, _ = ccmp_nonce(bytes(hdr) + ccmp)
    aad = bytearray(hdr)
    aad[0] &= 0x8F if (fc >> 2) & 3 == 2 else 0xFF          # subtype bits 4-6 of a data frame
    aad[1] &= 0xC7                                           # retry, power management, more data
    aad[1] |= 0x40
    aad[22] &= 0x0F; aad[23] = 0                              # sequence control: the fragment number only
    if qos:
        aad[hl - 2] &= 0x0F; aad[hl - 1] = 0                  # QoS control: the TID only
    return bytes(hdr) + ccmp + AESCCM(key, tag_length=8).encrypt(nonce, bytes(mac_plain[hl:]), bytes(aad))
