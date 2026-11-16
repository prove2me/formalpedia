-- Prove2me | Theorems.Thm_Kyprianou_exercise2_3_truncatedImpliesFiniteLaplace
-- name    : Kyprianou.exercise2_3_truncatedImpliesFiniteLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:54:04.984198+00:00
-- url     : https://prove2.me/theorems/fced4eaa-cd25-4cdf-85d9-c5c16ba3ddd2
-- title:
--   Finite truncated intensity implies finite Laplace compensator for all positive parameters
-- statement:
--   Finite truncated intensity implies finite Laplace compensator for all positive parameters. This is one direction of the exact equivalence in Kyprianou Exercise 2.3, with the original measurable-space, measure and nonnegative measurable function hypotheses, no new assumptions.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.3, printed pp. 62-63; author solutions at end

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

theorem exercise2_3_truncatedImpliesFiniteLaplace
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤ →
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤)      := by sorry

end Kyprianou
