-- Prove2me | Theorems.Thm_O3_lpPower_neg
-- name    : O3.lpPower_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:03.151045+00:00
-- url     : https://prove2.me/theorems/f1ab9154-d611-5a82-a00c-119e6eab98f0
-- title:
--   O3: lp Power neg
-- statement:
--   The O3 construction uses the lp Power neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L81-L83
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L81-L83

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpPower_neg (p : ℝ) {d : ℕ} (x : Point d) :
    lpPower p (-x) = lpPower p x := by sorry
