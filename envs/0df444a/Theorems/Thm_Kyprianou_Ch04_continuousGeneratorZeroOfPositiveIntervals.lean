-- Prove2me | Theorems.Thm_Kyprianou_Ch04_continuousGeneratorZeroOfPositiveIntervals
-- name    : Kyprianou.Ch04.continuousGeneratorZeroOfPositiveIntervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:56:32.814195+00:00
-- url     : https://prove2.me/theorems/eb14d57b-75d7-4583-a293-390bf8980b18
-- title:
--   Almost surely zero continuous generator residual under positive interval marginals
-- statement:
--   Any continuous real-valued generator residual which vanishes almost surely under a measure assigning positive mass to every nonempty open real interval vanishes pointwise. The full-support upgrade is the final analytical step of the generator identity in Kyprianou Chapter 4 Exercise 4.3 part (iii); the independent prior tasks must establish almost-sure generator equality and continuity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.3(iii); the positive-open-interval marginal assumption.

import Mathlib

open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch04.continuousGeneratorZeroOfPositiveIntervals
    (μ : Measure ℝ)
    (hFull : ∀ a b : ℝ, a < b → 0 < μ (Set.Ioo a b))
    (G : ℝ → ℝ) (hContinuous : Continuous G)
    (hAE : ∀ᵐ y ∂μ, G y = 0) :
    ∀ y : ℝ, G y = 0 := by
  sorry
