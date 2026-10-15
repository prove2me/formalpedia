-- Prove2me | Theorems.Thm_OAI_PiExponent_balanced_center_window_ratio
-- name    : OAI.PiExponent.balanced_center_window_ratio
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T09:06:13.374535+00:00
-- url     : https://prove2.me/theorems/01cfa28a-23ac-46ad-ba52-de1b6bd8c9d3
-- title:
--   Integer centers eventually fit the quadratic window
-- statement:
--   For positive theta below one and positive A with A squared below theta, any base R greater than one whose square is below theta divided by A squared admits a cutoff. At every natural exponent beyond that cutoff, a positive integer K lies strictly inside the quadratic window and gives the stated quotient lower bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem OAI.PiExponent.balanced_center_window_ratio
    (theta : ℚ) (A R : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hA : 0 < A) (hquadratic : A ^ 2 < (theta : ℝ))
    (hR : 1 < R)
    (hRsq : R ^ 2 < (theta : ℝ) / A ^ 2) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∃ K : ℕ, 0 < K ∧
        (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1 ∧
        R ^ m / (8 * ((m : ℝ) + 1)) <
          ((K : ℝ) * (theta : ℝ) ^ m) /
            (((m : ℝ) + 1) * A ^ m) := by sorry
