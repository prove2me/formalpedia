-- Prove2me | Theorems.Thm_Kyprianou_exercise2_3_finiteLaplaceImpliesTruncated
-- name    : Kyprianou.exercise2_3_finiteLaplaceImpliesTruncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:53:59.392006+00:00
-- url     : https://prove2.me/theorems/5f11ba84-d368-49e1-9b0e-12d36c4f09be
-- title:
--   Finite Laplace compensator at every positive parameter implies finite truncated intensity
-- statement:
--   Finite Laplace compensator at every positive parameter implies finite truncated intensity. This is one direction of the exact equivalence in Kyprianou Exercise 2.3, with the original measurable-space, measure and nonnegative measurable function hypotheses, no new assumptions.
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

theorem exercise2_3_finiteLaplaceImpliesTruncated
    {E : Type} [MeasurableSpace E] (η : Measure E)
    (f : E → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∀ (φ : ℝ), 0 < φ →
      (∫⁻ x, ENNReal.ofReal
        (1 - Real.exp (-φ * f x)) ∂η) < ⊤) →
      (∫⁻ x, ENNReal.ofReal (min 1 (f x)) ∂η) < ⊤      := by sorry

end Kyprianou
