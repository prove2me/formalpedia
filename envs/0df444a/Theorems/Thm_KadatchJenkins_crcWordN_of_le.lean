-- Prove2me | Theorems.Thm_KadatchJenkins_crcWordN_of_le
-- name    : KadatchJenkins.crcWordN_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:13:59.908317+00:00
-- url     : https://prove2.me/theorems/e939a2ab-c66b-4e56-b1ed-8a7a717911a3
-- title:
--   §4.11.3 — CrcWordN when D ≤ W
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \ge D$ and $N \ge 0$. For all polynomials $v(x)$ of degree less than $D$ and $m(x)$ of degree less than $W$,
--   $$\mathrm{CrcWordN}(m, v) = \Big(\big(v\,x^{W-D} + m\big)\,x^{(N-1)W+D}\Big) \bmod P,$$
--   where $\mathrm{CrcWordN}(m, v) = \big((v\,x^W + m\,x^D)\,x^{(N-1)W}\big) \bmod P$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 19–20, §4.11.3, CrcWordN for D ≤ W

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crcWordN_of_le (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hDW : P.natDegree ≤ W)
    (m v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) (hm : m.degree < (W : WithBot ℕ)) :
    crcWordN P W N m v = ((v * X ^ (W - P.natDegree) + m) * X ^ ((N - 1) * W + P.natDegree)) % P := by
  sorry

end KadatchJenkins
