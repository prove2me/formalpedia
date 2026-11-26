-- Prove2me | Theorems.Thm_O3_Stage2RouteB_pairing_scalar_right
-- name    : O3.Stage2RouteB.pairing_scalar_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:41.044667+00:00
-- url     : https://prove2.me/theorems/c728613a-277e-526c-8cd0-04aa27f71c21
-- title:
--   Stage2 Route B: pairing scalar right
-- statement:
--   The Stage2 Route B construction uses the pairing scalar right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L472-L474
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L472-L474

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.pairing_scalar_right {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing a (fun i ↦ r * b i) = r * pairing a b := by sorry
