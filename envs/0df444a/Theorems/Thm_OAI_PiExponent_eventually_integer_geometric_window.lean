-- Prove2me | Theorems.Thm_OAI_PiExponent_eventually_integer_geometric_window
-- name    : OAI.PiExponent.eventually_integer_geometric_window
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T09:25:55.202537+00:00
-- url     : https://prove2.me/theorems/594e00c9-2a13-440f-8913-11441dd3d0a1
-- title:
--   Eventually an integer fits between two geometric bounds
-- statement:
--   If 0 < theta < 1, b > 0, and b² theta < 1, then at every sufficiently large natural exponent m there is a positive integer K strictly above b^m/8 with K² theta^m < 1. The cutoff is necessary because the conclusion fails at m = 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.eventually_integer_geometric_window
    (theta b : ℝ) (htheta : 0 < theta) (htheta_one : theta < 1)
    (hb : 0 < b) (hgap : b ^ 2 * theta < 1) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∃ K : ℕ, 0 < K ∧
        (K : ℝ) ^ 2 * theta ^ m < 1 ∧ b ^ m / 8 < (K : ℝ) := by sorry
