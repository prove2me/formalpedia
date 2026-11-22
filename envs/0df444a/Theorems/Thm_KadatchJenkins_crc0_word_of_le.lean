-- Prove2me | Theorems.Thm_KadatchJenkins_crc0_word_of_le
-- name    : KadatchJenkins.crc0_word_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:05:46.358291+00:00
-- url     : https://prove2.me/theorems/d85cf1a4-6e58-4bf3-9d46-731f2a6944fa
-- title:
--   Eq. (8) — Byte-by-byte CRC when D ≤ W
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$ and $W \ge D$. For every $W$-bit message $M$ and every polynomial $v(x)$ of degree less than $D$,
--   $$\mathrm{CRC}_0(M, v) = \Big(\big(v(x)x^{W-D} + M(x)\big)x^D\Big) \bmod P,$$
--   and $\deg\big(v(x)x^{W-D} + M(x)\big) < W$. The lookup table $T$ that (8) indexes by this $W$-bit value is not formalized.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 9–10, §4.6, eq. (8) (Byte-by-byte CRC computation, D ≤ W)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc0_word_of_le (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hDW : P.natDegree ≤ W)
    (M : Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    crc0 P M v = ((v * X ^ (W - P.natDegree) + M.poly) * X ^ P.natDegree) % P ∧
      (v * X ^ (W - P.natDegree) + M.poly).degree < (W : WithBot ℕ) := by
  sorry

end KadatchJenkins
