-- Prove2me | Theorems.Thm_O3_pairing_neg_left
-- name    : O3.pairing_neg_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:04.284813+00:00
-- url     : https://prove2.me/theorems/cf314628-f8e2-55ab-b4d2-ded4f1cbeff6
-- title:
--   O3: pairing neg left
-- statement:
--   The O3 construction uses the pairing neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L92-L94
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L92-L94

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_neg_left {d : ℕ} (x y : Point d) :
    pairing (-x) y = -pairing x y := by sorry
