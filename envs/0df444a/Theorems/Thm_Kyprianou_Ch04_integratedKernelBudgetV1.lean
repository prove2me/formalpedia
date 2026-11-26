-- Prove2me | Theorems.Thm_Kyprianou_Ch04_integratedKernelBudgetV1
-- name    : Kyprianou.Ch04.integratedKernelBudgetV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:29.761307+00:00
-- url     : https://prove2.me/theorems/081eb2ea-665f-5b14-956a-a22d0abed17a
-- title:
--   Integrated two-band quadratic energy bound
-- statement:
--   Integrated two-band quadratic energy bound
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem integratedKernelBudgetV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) (T : NNReal)
    (H : ℝ → ℝ → Ω → ℝ) (S : Ω → ℝ) (A B : ℝ → ℝ)
    (hA : Integrable A ν) (hB : Integrable B ν) (hS : Integrable S P)
    (K : ℝ)
    (h : ∀ᵐ ω ∂P, ∀ s ∈ Ioc (0 : ℝ) (T : ℝ), ∀ z : ℝ,
      (H s z ω)^2 ≤ K^2 * (A z + B z * S ω)) :
    (∫ ω, ∫ s in Ioc (0 : ℝ) (T : ℝ), ∫ z, (H s z ω)^2 ∂ν ∂volume ∂P) ≤
      K^2 * (T : ℝ) * ((∫ z, A z ∂ν) + (∫ z, B z ∂ν) * ∫ ω, S ω ∂P) := by
  sorry
end Kyprianou.Ch04
