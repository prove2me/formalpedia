-- Prove2me | Theorems.Thm_O3_Stage2RouteB_abs_dualityMap_coordinate
-- name    : O3.Stage2RouteB.abs_dualityMap_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:20:46.805581+00:00
-- url     : https://prove2.me/theorems/0aa31335-19b0-5fcd-aa2c-19ea598471a4
-- title:
--   Stage2 Route B: abs duality Map coordinate
-- statement:
--   The Stage2 Route B construction uses the abs duality Map coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L303-L310
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L303-L310

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.abs_dualityMap_coordinate {p : ℝ} (hp : 1 < p) {d : ℕ}
    {x : Point d} (hx : x ≠ 0) (i : Fin d) :
    |dualityMap p x i| =
      (lpNorm p x) ^ (2 - p) * |x i| ^ (p - 1) := by sorry
