-- Prove2me | Theorems.Thm_LL_Decomp1525c_swap
-- name    : LL_Decomp1525c.swap
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:03:40.048716+00:00
-- url     : https://prove2.me/theorems/17ed2468-3a29-4ed7-8c06-032d2944a26b
-- title:
--   Exchange the prime sum and integral
-- statement:
--   For every real $x\ge6$, $\sum_{p\in P_1(x)}\log p\int_{x-p}^{2x-p}du/\log u=\int_3^{2x}I_x(u)/\log u\,du$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem swap (x : ℝ) (hx : 6 ≤ x) :
    ∑ p ∈ P1V x, Real.log p * ∫ u in (x - p)..(2 * x - p), 1 / Real.log u =
      ∫ u in (3 : ℝ)..(2 * x), thetaI x u / Real.log u := by sorry
end LL_Decomp1525c
