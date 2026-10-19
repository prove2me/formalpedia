-- Prove2me | Theorems.Thm_MeasureTheory_eventwiseLaw_integral_test_identity
-- name    : MeasureTheory.eventwiseLaw_integral_test_identity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:34:39.027908+00:00
-- url     : https://prove2.me/theorems/2db7e82f-b49f-42b3-a43c-e8f61df8dce2
-- title:
--   Extend eventwise conditional laws to test-integral identities
-- statement:
--   Under the eventwise conditional-law hypotheses and the almost-sure bound, the realized observable and its kernel mean are integrable; the kernel mean is measurable with respect to the conditioning sigma algebra almost everywhere; and their integrals agree on every conditioning-measurable set.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory
open scoped MeasureTheory

theorem MeasureTheory.eventwiseLaw_integral_test_identity
    {Ω : Type*} {E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → E) (hX : @Measurable Ω E mΩ mE X)
    (ν : Ω → Measure E) (hν : ∀ ω, IsProbabilityMeasure (ν ω))
    (hLaw : ∀ B : Set E, MeasurableSet B →
      P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P]
        fun ω => (ν ω B).toReal)
    (f : E → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ω, ∀ᵐ x ∂(ν ω), ‖f x‖ ≤ C) :
    Integrable (fun ω => f (X ω)) P ∧
      Integrable (fun ω => ∫ x, f x ∂(ν ω)) P ∧
      AEStronglyMeasurable[m] (fun ω => ∫ x, f x ∂(ν ω)) P ∧
      ∀ s : Set Ω, MeasurableSet[m] s →
        ∫ ω in s, (∫ x, f x ∂(ν ω)) ∂P =
          ∫ ω in s, f (X ω) ∂P := by sorry
