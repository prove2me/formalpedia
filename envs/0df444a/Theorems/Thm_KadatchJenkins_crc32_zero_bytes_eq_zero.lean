-- Prove2me | Theorems.Thm_KadatchJenkins_crc32_zero_bytes_eq_zero
-- name    : KadatchJenkins.crc32_zero_bytes_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:39:32.009664+00:00
-- url     : https://prove2.me/theorems/250d4509-f7f2-40b7-adcd-3ba19ece612e
-- title:
--   Kadatch–Jenkins, p. 3 — CRC-32 with initial value 0 of 2^32 − 1 zero bytes is 0
-- statement:
--   Let $P(x) = x^{32} + x^{26} + x^{23} + x^{22} + x^{16} + x^{12} + x^{11} + x^{10} + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1$ over $\mathrm{GF}(2)$, the CRC-32 polynomial (its coefficients below $x^{32}$ are `0x04C11DB7`), and $u(x) = \sum_{k=0}^{31} x^k$, the usual conditioning polynomial of eq. (2). Let $M$ be the message of $2^{32} - 1$ zero bytes, that is $8(2^{32} - 1)$ zero bits. Then the CRC of eq. (1) with initial value $v(x) = 0$ is zero:
--   $$\mathrm{CRC}_u\big(M(x), 0\big) = \big((0 - u(x))\cdot x^{|M|} + M(x)\cdot x^{32} + u(x)\big) \bmod P(x) = 0.$$
--
--   This refutes the sentence of A. Kadatch and B. Jenkins, *Everything we know about CRC but afraid to forget* (2010), §1, p. 3: “The use of the non-zero value of $u(x)$ guarantees that the CRC of a sequence of zeroes is different from zero.” Since $M(x) = 0$, the CRC equals $u(x)\,(1 - x^{|M|}) \bmod P(x)$, and it vanishes because $x$ has order dividing $2^{32} - 1$ modulo $P(x)$. The bundle's `crc`, `stdU` and `Message.ofBytes` are those of the mission (bundle `KadatchJenkinsCrc`).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 3, §1, the sentence on the non-zero u(x) and sequences of zeroes, refuted for CRC-32 (counterexample, not in the paper)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc32_zero_bytes_eq_zero :
    crc (X ^ 32 + X ^ 26 + X ^ 23 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 +
          X ^ 5 + X ^ 4 + X ^ 2 + X + 1) (stdU 32)
        (Message.ofBytes (List.replicate (2 ^ 32 - 1) 0#8)) 0 = 0 := by
  sorry

end KadatchJenkins
