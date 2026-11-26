-- Prove2me | Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
-- name    : O3.Stage2RouteD.pairing_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:29.705813+00:00
-- url     : https://prove2.me/theorems/b96c8068-b575-52d8-b054-8a850622dddc
-- title:
--   Stage2 Route D: pairing smul left
-- statement:
--   The Stage2 Route D construction uses the pairing smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L22-L24
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L22-L24

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD

theorem O3.Stage2RouteD.pairing_smul_left {d : ℕ} (a : ℝ) (x y : Point d) :
    pairing (a • x) y = a * pairing x y := by sorry
