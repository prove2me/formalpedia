-- Prove2me | Theorems.Thm_OAI_PiExponent_exp_beats_quadratic_after
-- name    : OAI.PiExponent.exp_beats_quadratic_after
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:16:23.670557+00:00
-- url     : https://prove2.me/theorems/01dd9e0e-2b4e-4de3-893c-1f5fbd17d0b1
-- title:
--   An exponential eventually exceeds a positive quadratic multiple
-- statement:
--   For any real base greater than one, positive real coefficient, and natural cutoff, some exponent at or beyond the cutoff makes the exponential exceed that coefficient times the square of one plus the exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.exp_beats_quadratic_after
    (R C : ℝ) (hR : 1 < R) (M : ℕ) (hC : 0 < C) :
    ∃ m : ℕ, M ≤ m ∧ C * ((m : ℝ) + 1) ^ 2 < R ^ m := by sorry
