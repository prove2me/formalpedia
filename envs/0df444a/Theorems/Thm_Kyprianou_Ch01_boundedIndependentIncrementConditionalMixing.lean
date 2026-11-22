-- Prove2me | Theorems.Thm_Kyprianou_Ch01_boundedIndependentIncrementConditionalMixing
-- name    : Kyprianou.Ch01.boundedIndependentIncrementConditionalMixing
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:03:10.05563+00:00
-- url     : https://prove2.me/theorems/b45c75f1-f650-4da3-8941-8c32d90f8f28
-- title:
--   Conditional expectation of a bounded measurable function of an adapted state plus an independent future increment
-- statement:
--   Standard bounded conditional-mixing lemma: if Y is measurable in a sub sigma algebra m of the ambient space, Z is measurable and independent of m, and f is globally measurable and bounded, then conditional expectation of f(Y+Z) given m is the integral of the shifted function over the independent Z law evaluated at Y. Prove first for finite simple measurable Y via conditional expectation and independence, then approximate a general Y using measurable simple functions and dominated convergence. This supplies the abstract conditional step for the exact Brownian McKean right-natural transition identity without assuming any Brownian Markov conclusion.
-- source:
--   Conditional expectation with independent increments, stochastic processes and Markov transition kernels.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
set_option autoImplicit false

theorem Kyprianou.Ch01.boundedIndependentIncrementConditionalMixing
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ (inferInstance : MeasurableSpace Ω))
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ m (inferInstance : MeasurableSpace ℝ) Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z (inferInstance : MeasurableSpace ℝ)) m P) :
    P[(fun ω => f (Y ω + Z ω)) | m] =ᵐ[P]
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) := by sorry
