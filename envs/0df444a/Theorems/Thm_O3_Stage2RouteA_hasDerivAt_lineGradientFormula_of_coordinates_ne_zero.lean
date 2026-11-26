-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_lineGradientFormula_of_coordinates_ne_zero
-- name    : O3.Stage2RouteA.hasDerivAt_lineGradientFormula_of_coordinates_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:52.735956+00:00
-- url     : https://prove2.me/theorems/7eb64bb4-3a83-5de1-b8a6-bc8136d780a6
-- title:
--   Stage2 Route A: has Deriv At line Gradient Formula of coordinates ne zero
-- statement:
--   Exact Hessian formula at points where the vector and all coordinates avoid
--   the real-power singularities.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L335-L372
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L335-L372

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_lineGradientFormula_of_coordinates_ne_zero
    {p : ℝ} (hp : 1 < p) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0)
    (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (lineGradientFormula p x h)
      ((2 - p) * (linePower p x h t) ^ (2 / p - 2) *
          (linePowerPair p x h t) ^ (2 : ℕ) +
        (p - 1) * (linePower p x h t) ^ (2 / p - 1) *
          weightedSquareSum p x h t) t := by sorry
