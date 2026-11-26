-- Prove2me | Theorems.Thm_O3_pairing_neg_right
-- name    : O3.pairing_neg_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:15.86824+00:00
-- url     : https://prove2.me/theorems/b25a756a-8351-4049-a3d7-1c4bb8c077ff
-- title:
--   O3: pairing neg right
-- statement:
--   The O3 construction uses the pairing neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L96-L98
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L96-L98

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_neg_right {d : ℕ} (x y : Point d) :
    pairing x (-y) = -pairing x y := by sorry
