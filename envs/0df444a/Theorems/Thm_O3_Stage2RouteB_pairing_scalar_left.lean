-- Prove2me | Theorems.Thm_O3_Stage2RouteB_pairing_scalar_left
-- name    : O3.Stage2RouteB.pairing_scalar_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:19:23.640846+00:00
-- url     : https://prove2.me/theorems/8a057127-87c8-521a-98c6-2ef7f88a833d
-- title:
--   Stage2 Route B: pairing scalar left
-- statement:
--   The Stage2 Route B construction uses the pairing scalar left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L464-L466
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L464-L466

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.pairing_scalar_left {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing (fun i ↦ r * a i) b = r * pairing a b := by sorry
