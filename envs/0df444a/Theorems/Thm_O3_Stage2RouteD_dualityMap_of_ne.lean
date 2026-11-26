-- Prove2me | Theorems.Thm_O3_Stage2RouteD_dualityMap_of_ne
-- name    : O3.Stage2RouteD.dualityMap_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:40.311046+00:00
-- url     : https://prove2.me/theorems/49bc5ba2-6da9-5404-bef9-ff38fbf8ad63
-- title:
--   Stage2 Route D: duality Map of ne
-- statement:
--   The Stage2 Route D construction uses the duality Map of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L57-L61
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L57-L61

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD

theorem O3.Stage2RouteD.dualityMap_of_ne {p : ℝ} (hp : 0 < p) {d : ℕ} {u : Point d}
    (hu : u ≠ 0) :
    dualityMap p u = fun i ↦ (lpNorm p u) ^ (2 - p) *
      (|u i| ^ (p - 2) * u i) := by sorry
