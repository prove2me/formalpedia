-- Prove2me | Theorems.Thm_OAI_PiExponent_rational_scale_error_control_nat_n
-- name    : OAI.PiExponent.rational_scale_error_control_nat_n
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T04:59:17.037476+00:00
-- url     : https://prove2.me/theorems/f26c3b79-f4c7-4c69-9ed4-79113f04db94
-- title:
--   Choose an integer scale controlling a nonnegative reciprocal error
-- statement:
--   For nonnegative d and positive g, choose a positive natural number n so that d/n is strictly less than g/4.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.rational_scale_error_control_nat_n
    (d g : ℝ) (hd : 0 ≤ d) (hg : 0 < g) :
    ∃ n : ℕ, 0 < n ∧ d / (n : ℝ) < g / 4 := by sorry
