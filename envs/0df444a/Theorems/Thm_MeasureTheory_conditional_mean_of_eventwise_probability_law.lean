-- Prove2me | Theorems.Thm_MeasureTheory_conditional_mean_of_eventwise_probability_law
-- name    : MeasureTheory.conditional_mean_of_eventwise_probability_law
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T18:13:12.010802+00:00
-- url     : https://prove2.me/theorems/c3052137-e025-41a3-8e3e-d73cc39cef02
-- title:
--   Extend an eventwise conditional probability law to bounded measurable observables
-- statement:
--   If the conditional probability of every measurable event of X agrees almost surely with a family of probability measures, then any measurable real observable uniformly bounded almost surely under every measure in that family is integrable when evaluated at X, and its conditional expectation equals its integral against that family. The bound may be zero, and the observable may take either sign.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory
open scoped MeasureTheory

theorem MeasureTheory.conditional_mean_of_eventwise_probability_law
    {Ω : Type*} {E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Ω → E) (hX : Measurable X)
    (ν : Ω → Measure E) (hν : ∀ ω, IsProbabilityMeasure (ν ω))
    (hLaw : ∀ B : Set E, MeasurableSet B →
      P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[P]
        fun ω => (ν ω B).toReal)
    (f : E → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ω, ∀ᵐ x ∂(ν ω), ‖f x‖ ≤ C) :
    Integrable (fun ω => f (X ω)) P ∧
      P[(fun ω => f (X ω)) | m] =ᵐ[P] fun ω => ∫ x, f x ∂(ν ω) := by sorry
