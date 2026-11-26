-- Prove2me | Theorems.Thm_O3_Stage2RouteD_pairing_smul_right
-- name    : O3.Stage2RouteD.pairing_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:38.638205+00:00
-- url     : https://prove2.me/theorems/363a3312-f308-53d6-a0d2-856069cade77
-- title:
--   Stage2 Route D: pairing smul right
-- statement:
--   The Stage2 Route D construction uses the pairing smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L26-L28
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L26-L28

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD

theorem O3.Stage2RouteD.pairing_smul_right {d : ℕ} (a : ℝ) (x y : Point d) :
    pairing x (a • y) = a * pairing x y := by sorry
