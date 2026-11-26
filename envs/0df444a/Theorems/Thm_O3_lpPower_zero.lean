-- Prove2me | Theorems.Thm_O3_lpPower_zero
-- name    : O3.lpPower_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:05.793857+00:00
-- url     : https://prove2.me/theorems/eacb4e04-d008-46a0-8f8d-f7edcaf92509
-- title:
--   O3: lp Power zero
-- statement:
--   The O3 construction uses the lp Power zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L46-L48
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L46-L48

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpPower_zero {p : ℝ} (hp : p ≠ 0) {d : ℕ} :
    lpPower p (0 : Point d) = 0 := by sorry
