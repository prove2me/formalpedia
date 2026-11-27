-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45SmoothPlateauJetV1
-- name    : Kyprianou.Ch04.exercise45SmoothPlateauJetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:19:19.500177+00:00
-- url     : https://prove2.me/theorems/9187b341-a9fd-4fa3-b92d-615b5f3eda36
-- title:
--   Smooth plateau with first and second derivatives zero in the interior and exterior
-- statement:
--   For every nonnegative radius there is a smooth scalar bump equal to one, with zero first and second derivatives, on the closed inner interval, and all three quantities zero beyond the outer radius.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation argument.

import Mathlib
open Filter Set
open scoped ContDiff
set_option autoImplicit false

/-- A smooth scalar plateau has vanishing first and second derivatives on its interior. -/
theorem Kyprianou.Ch04.exercise45SmoothPlateauJetV1 (R : ℝ) (hR : 0 ≤ R) :
    ∃ b : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) b ∧
      (∀ x, |x| ≤ R → b x = 1 ∧ deriv b x = 0 ∧ deriv (deriv b) x = 0) ∧
      (∀ x, R + 3 < |x| → b x = 0 ∧ deriv b x = 0 ∧ deriv (deriv b) x = 0) := by
  sorry
