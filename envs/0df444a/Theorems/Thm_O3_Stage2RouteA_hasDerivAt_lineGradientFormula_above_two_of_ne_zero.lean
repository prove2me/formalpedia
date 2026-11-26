-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_lineGradientFormula_above_two_of_ne_zero
-- name    : O3.Stage2RouteA.hasDerivAt_lineGradientFormula_above_two_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:43.056412+00:00
-- url     : https://prove2.me/theorems/a89a8a03-e8a9-4d7a-80cc-e1b79a058644
-- title:
--   Stage2 Route A: has Deriv At line Gradient Formula above two of ne zero
-- statement:
--   Above two, the same exact normalized Hessian formula needs only the whole
--   vector to be nonzero; scalar zero coordinates are covered by
--   `hasDerivAt_scalarJ_zero`.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L377-L412
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L377-L412

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_lineGradientFormula_above_two_of_ne_zero
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0) :
    HasDerivAt (lineGradientFormula q x h)
      ((2 - q) * (linePower q x h t) ^ (2 / q - 2) *
          (linePowerPair q x h t) ^ (2 : ℕ) +
        (q - 1) * (linePower q x h t) ^ (2 / q - 1) *
          weightedSquareSum q x h t) t := by sorry
