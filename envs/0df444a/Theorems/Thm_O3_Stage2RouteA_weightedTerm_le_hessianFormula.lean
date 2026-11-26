-- Prove2me | Theorems.Thm_O3_Stage2RouteA_weightedTerm_le_hessianFormula
-- name    : O3.Stage2RouteA.weightedTerm_le_hessianFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:16.863445+00:00
-- url     : https://prove2.me/theorems/da193846-a7d5-5f44-897a-76e8fc806db7
-- title:
--   Stage2 Route A: weighted Term le hessian Formula
-- statement:
--   The first Hessian term is nonnegative throughout the frozen range
--   `p ≤ 2`; hence only the weighted Hölder term remains for the pointwise lower
--   bound.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L469-L484
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L469-L484

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.weightedTerm_le_hessianFormula {p : ℝ} (hp2 : p ≤ 2) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    (p - 1) * linePower p x h t ^ (2 / p - 1) *
        weightedSquareSum p x h t ≤
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
          linePowerPair p x h t ^ (2 : ℕ) +
        (p - 1) * linePower p x h t ^ (2 / p - 1) *
          weightedSquareSum p x h t := by sorry
