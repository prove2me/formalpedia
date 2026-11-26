-- Prove2me | Theorems.Thm_O3_lpPower_pos_of_ne_zero
-- name    : O3.lpPower_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:22.014692+00:00
-- url     : https://prove2.me/theorems/33c5758a-b885-4a71-b471-83550d3a72d5
-- title:
--   O3: lp Power pos of ne zero
-- statement:
--   The O3 construction uses the lp Power pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L54-L66
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Geometry.lean#L54-L66

import Mathlib
import Definitions.Def_O3_Geometry
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpPower_pos_of_ne_zero {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpPower p x := by sorry
