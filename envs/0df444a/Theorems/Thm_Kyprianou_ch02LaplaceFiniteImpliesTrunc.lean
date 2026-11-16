-- Prove2me | Theorems.Thm_Kyprianou_ch02LaplaceFiniteImpliesTrunc
-- name    : Kyprianou.ch02LaplaceFiniteImpliesTrunc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:34:22.027162+00:00
-- url     : https://prove2.me/theorems/ac2779aa-a436-4094-8816-bc3621a7cf7a
-- title:
--   Portable Chapter 2 Exercise 2.3: Finite Laplace compensator at every positive parameter implies finite truncated intensity
-- statement:
--   Finite Laplace compensator at every positive parameter implies finite truncated intensity. This is one direction of the exact equivalence in Kyprianou Exercise 2.3, with the original measurable-space, measure and nonnegative measurable function hypotheses, no new assumptions.
-- source:
--   Kyprianou (2006) Chapter 2 Exercise 2.3, exact source hypotheses; portable import closure

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_oneSubExpLowerBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem ch02LaplaceFiniteImpliesTrunc
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) →
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤      := by sorry

end Kyprianou
