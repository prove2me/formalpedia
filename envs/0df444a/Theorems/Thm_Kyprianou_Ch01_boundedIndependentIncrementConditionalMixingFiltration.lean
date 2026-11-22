-- Prove2me | Theorems.Thm_Kyprianou_Ch01_boundedIndependentIncrementConditionalMixingFiltration
-- name    : Kyprianou.Ch01.boundedIndependentIncrementConditionalMixingFiltration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:11:51.158655+00:00
-- url     : https://prove2.me/theorems/556a2d3b-17c0-4015-8c53-f7de31977aae
-- title:
--   Bounded independent-increment conditional mixing relative to a subfiltration of the ambient probability space
-- statement:
--   Correctly typed bounded conditional mixing over a filtration F of the original ambient probability space. Given Y strongly measurable at time s, an ambient-measurable independent future increment Z, and measurable bounded payoff f, conditional expectation given F_s of f(Y+Z) equals the integral of the shifted payoff against the original independent Z law, evaluated at the current Y. The named filtration structurally guarantees F_s≤ambient so a distinct `MeasurableSpace Ω` parameter cannot shadow the original ambient instance. The original separately published helper has a problematic sub-σ-algebra elaboration and must not be imported. Prove this actual stochastic conditional-mixing statement with finite simple-state approximations, conditional independence and bounded convergence; this is a necessary child in the exact mission-linked McKean right-natural transition theorem.
-- source:
--   Conditional expectation under independent increments for adapted states, Kyprianou (2006) Chapter 1.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.boundedIndependentIncrementConditionalMixingFiltration
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (s : ℝ≥0)
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ (F s) inferInstance Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P) :
    P[(fun ω => f (Y ω + Z ω)) | F s] =ᵐ[P]
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) := by sorry
