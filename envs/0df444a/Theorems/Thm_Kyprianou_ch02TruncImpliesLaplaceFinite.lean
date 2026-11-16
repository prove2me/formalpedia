-- Prove2me | Theorems.Thm_Kyprianou_ch02TruncImpliesLaplaceFinite
-- name    : Kyprianou.ch02TruncImpliesLaplaceFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:34:21.583179+00:00
-- url     : https://prove2.me/theorems/8f4b3ecb-2490-4b8d-b53d-62811b3372f0
-- title:
--   Portable Chapter 2 Exercise 2.3: Finite truncated intensity implies finite Laplace compensator for all positive parameters
-- statement:
--   Finite truncated intensity implies finite Laplace compensator for all positive parameters. This is one direction of the exact equivalence in Kyprianou Exercise 2.3, with the original measurable-space, measure and nonnegative measurable function hypotheses, no new assumptions.
-- source:
--   Kyprianou (2006) Chapter 2 Exercise 2.3, exact source hypotheses; portable import closure

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_oneSubExpLowerBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem ch02TruncImpliesLaplaceFinite
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ →
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤)      := by sorry

end Kyprianou
