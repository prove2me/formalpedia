-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clockAverageBoundsNNReal
-- name    : Kyprianou.Ch04.clockAverageBoundsNNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:35:05.866249+00:00
-- url     : https://prove2.me/theorems/63194cc6-56ba-4ab5-96df-43c235a47dec
-- title:
--   Bounded antitone clock reward and early-clock error
-- statement:
--   Use the probability-normalised integral of a constant for the lower bound. The pointwise upper bound is the reward at the cutoff plus the indicator of an early clock. Integrate this inequality.
-- source:
--   Kyprianou (2006), Chapter 4, Corollaries 4.9 and 4.12

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.clockAverageBoundsNNReal
    (mu : Measure NNReal) [IsProbabilityMeasure mu]
    (f : NNReal → ℝ) (ell : ℝ)
    (hf : Integrable f mu) (hanti : Antitone f)
    (hlow : ∀ t, ell ≤ f t) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ 1) (T : NNReal) :
    ell ≤ (∫ t, f t ∂mu) ∧
      (∫ t, f t ∂mu) ≤ f T + (mu (Iio T)).toReal := by
  sorry
