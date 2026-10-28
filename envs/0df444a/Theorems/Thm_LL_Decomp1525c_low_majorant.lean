-- Prove2me | Theorems.Thm_LL_Decomp1525c_low_majorant
-- name    : LL_Decomp1525c.low_majorant
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:05:53.848712+00:00
-- url     : https://prove2.me/theorems/693cb0cf-0f93-486f-bdd0-77693ce9ed04
-- title:
--   Bound the lower majorant integral
-- statement:
--   For every real $x\ge10^{52}$, with $t(u)=\max(x-u,2)$, $\int_3^x [x/(40\log x)+t(u)/(40\log t(u))+678412]/\log u\,du\le x^2/(20\log^2x)$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem low_majorant (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in (3 : ℝ)..x, (x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by sorry
end LL_Decomp1525c
