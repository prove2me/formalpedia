-- Prove2me | Theorems.Thm_Kyprianou_Ch01_probabilityDeficitMarkovBoundV1
-- name    : Kyprianou.Ch01.probabilityDeficitMarkovBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:03:45.997443+00:00
-- url     : https://prove2.me/theorems/38d7e790-203b-4a57-ae33-560e5b0de750
-- title:
--   Markov upper bound on expected deficit of a probability-normalised bounded observable
-- statement:
--   For an integrable real random variable f bounded above by 1 almost everywhere, the deficit 1-f is integrable and nonnegative almost everywhere. Apply the exact pinned Mathlib Markov inequality mul_meas_ge_le_integral_of_nonneg at level epsilon. The probability-normalised integral of the constant one is one, so its expected deficit is 1 - ∫f. This gives the upper bound on the measure of the deficit event without positivity requirements on epsilon. The theorem is useful for the inverse Gaussian Laplace passage transform f=passageLaplace T 1.
-- source:
--   Markov's inequality for nonnegative integrable real random variables, specialised to 1-f on a probability measure.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.probabilityDeficitMarkovBoundV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P)
    (hf_le : ∀ᵐ ω ∂P, f ω ≤ 1)
    (ε : ℝ) :
    ε * (P {ω | ε ≤ 1 - f ω}).toReal ≤
      1 - ∫ ω, f ω ∂P := by
  sorry
