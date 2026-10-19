-- Prove2me | Theorems.Thm_MeasureTheory_conditional_mean_of_eventwise_probability_law_ambient
-- name    : MeasureTheory.conditional_mean_of_eventwise_probability_law_ambient
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:29:07.49473+00:00
-- url     : https://prove2.me/theorems/c35db119-8aed-4c50-b362-6463cf71442d
-- title:
--   Extend an eventwise conditional law to bounded ambient-measurable observables
-- statement:
--   An ambient-measurable random variable whose eventwise conditional probabilities agree with a family of probability measures has the corresponding conditional-mean identity for every measurable real observable uniformly bounded almost surely under that family. The realized observable is integrable. It need not be measurable for the conditioning sigma algebra, and the bound may be zero.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory
open scoped MeasureTheory

theorem MeasureTheory.conditional_mean_of_eventwise_probability_law_ambient
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
      P[(fun ω => f (X ω)) | m] =ᵐ[P] fun ω => ∫ x, f x ∂(ν ω) := by sorry
