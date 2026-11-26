-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePowerPair_of_coordinates_ne_zero
-- name    : O3.Stage2RouteA.hasDerivAt_linePowerPair_of_coordinates_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:08.913812+00:00
-- url     : https://prove2.me/theorems/6f0e3dc7-4efa-433d-b817-e99d93cda10f
-- title:
--   Stage2 Route A: has Deriv At line Power Pair of coordinates ne zero
-- statement:
--   The Stage2 Route A construction uses the has Deriv At line Power Pair of coordinates ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L211-L236
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L211-L236

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_linePowerPair_of_coordinates_ne_zero {p : ℝ} {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (linePowerPair p x h)
      ((p - 1) * weightedSquareSum p x h t) t := by sorry
