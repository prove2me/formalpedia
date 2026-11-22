-- Prove2me | Theorems.Thm_KadatchJenkins_pow2k_zero_and_succ
-- name    : KadatchJenkins.pow2k_zero_and_succ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:03:20.208991+00:00
-- url     : https://prove2.me/theorems/27743175-8e99-477f-bcbf-d2b7609de14a
-- title:
--   §4.4 — The recurrence for Pow2k
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $\mathrm{Pow2k}(k) = x^{2^k} \bmod P$ (eq. (6)). Then $\mathrm{Pow2k}(0) = x \bmod P$, and for every $k \ge 0$,
--   $$\mathrm{Pow2k}(k+1) = \big(\mathrm{Pow2k}(k)\big)^2 \bmod P.$$
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 8–9, §4.4, eq. (6) and the recurrence for Pow2k(k)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem pow2k_zero_and_succ (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) :
    pow2k P 0 = X % P ∧ ∀ k, pow2k P (k + 1) = pow2k P k ^ 2 % P := by
  sorry

end KadatchJenkins
