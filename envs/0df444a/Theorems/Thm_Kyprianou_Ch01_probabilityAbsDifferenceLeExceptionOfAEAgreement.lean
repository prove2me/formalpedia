-- Prove2me | Theorems.Thm_Kyprianou_Ch01_probabilityAbsDifferenceLeExceptionOfAEAgreement
-- name    : Kyprianou.Ch01.probabilityAbsDifferenceLeExceptionOfAEAgreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:11:39.428741+00:00
-- url     : https://prove2.me/theorems/54872471-15c2-4823-9003-5d0dc3161a28
-- title:
--   Absolute probability difference bounded by exceptional event under almost-sure agreement
-- statement:
--   If two events agree outside a third exceptional event almost surely under a probability measure, then the absolute difference of their probabilities is at most the probability of the exceptional event. Use a.e. set inclusion, outer measure union bounds, and finite-measure real conversion; no measurability assumptions on A, B or E are needed.
-- source:
--   Mathlib measure_mono_ae, measure_union_le and probability-measure finiteness

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.probabilityAbsDifferenceLeExceptionOfAEAgreement
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A B E : Set Ω)
    (hAgree : ∀ᵐ ω ∂Q,
      ω ∉ E → (ω ∈ A ↔ ω ∈ B)) :
    |(Q A).toReal - (Q B).toReal| ≤ (Q E).toReal := by
  sorry
