-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightMixingRegularityV1
-- name    : Kyprianou.Ch01.mckeanRightMixingRegularityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:49:19.959496+00:00
-- url     : https://prove2.me/theorems/14598df3-62d9-4f75-b8a5-6afdb777a741
-- title:
--   McKean independent-increment mixing: bounded shifted-payoff integrability and adapted measurable integral
-- statement:
--   For bounded measurable payoff of an adapted state and an independent measurable increment, prove integrability of the current and shifted payoff and measurability of the shifted-integral function relative to the underlying filtration. This provides the regularity side of the conditional expectation uniqueness argument for the right-continuous McKean mission.
-- source:
--   Kyprianou (2006), Theorem 1.13, regularity in conditional mixing argument.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightMixingRegularityV1
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
    Integrable (fun ω => f (Y ω + Z ω)) P ∧
    Integrable (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) P ∧
    AEStronglyMeasurable[F s]
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) P := by sorry
