-- Prove2me | Theorems.Thm_LL_Decomp1525c_high_majorant
-- name    : LL_Decomp1525c.high_majorant
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:06:41.408301+00:00
-- url     : https://prove2.me/theorems/93218938-e7ea-4651-9d7a-c213f9c9ce33
-- title:
--   Bound the upper majorant integral
-- statement:
--   For every real $x\ge10^{52}$, with $s(u)=\max(\min(x-3,2x-u),2)$, $\int_x^{2x}[s(u)/(40\log s(u))+678412]/\log u\,du\le x^2/(20\log^2x)$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem high_majorant (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in x..(2 * x), (max (min (x - 3) (2 * x - u)) 2 /
        (40 * Real.log (max (min (x - 3) (2 * x - u)) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by sorry
end LL_Decomp1525c
