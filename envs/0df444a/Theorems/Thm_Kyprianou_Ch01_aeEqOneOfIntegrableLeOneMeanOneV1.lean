-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aeEqOneOfIntegrableLeOneMeanOneV1
-- name    : Kyprianou.Ch01.aeEqOneOfIntegrableLeOneMeanOneV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:28:49.284701+00:00
-- url     : https://prove2.me/theorems/ad0e39f1-f04b-4ebb-8e60-62d4e8cffeee
-- title:
--   An integrable random variable bounded above by one and of mean one equals one almost surely
-- statement:
--   For a real integrable random variable on a probability space bounded above by one almost everywhere, expectation equal to one forces the variable to equal one almost surely. Subtract from the constant-one function, apply integrable subtraction, integral of the constant one, and Mathlib integral_eq_zero_iff_of_nonneg_ae to the nonnegative deficit.
-- source:
--   Nonnegative integrable deficit criterion and probability normalisation.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.aeEqOneOfIntegrableLeOneMeanOneV1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ)
    (hf : Integrable f P)
    (hfLe : ∀ᵐ ω ∂P, f ω ≤ 1)
    (hMean : (∫ ω, f ω ∂P) = 1) :
    ∀ᵐ ω ∂P, f ω = 1 := by sorry
