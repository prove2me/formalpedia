-- Prove2me | Theorems.Thm_O3_Stage2RouteB_lpNorm_scalar_mul
-- name    : O3.Stage2RouteB.lpNorm_scalar_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:15.702745+00:00
-- url     : https://prove2.me/theorems/1e70e442-5127-4c17-a77a-200e7dc2d503
-- title:
--   Stage2 Route B: lp Norm scalar mul
-- statement:
--   The Stage2 Route B construction uses the lp Norm scalar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L423-L430
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L423-L430

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.lpNorm_scalar_mul {r a : ℝ} (hr : 0 < r) {d : ℕ} (z : Point d) :
    lpNorm r (fun i ↦ a * z i) = |a| * lpNorm r z := by sorry
