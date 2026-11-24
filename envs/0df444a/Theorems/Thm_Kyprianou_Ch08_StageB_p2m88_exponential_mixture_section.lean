-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_mixture_section
-- name    : Kyprianou.Ch08.StageB.p2m88_exponential_mixture_section
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:22:31.90071+00:00
-- url     : https://prove2.me/theorems/517ef128-63de-4305-abbf-7e4d0dbe430c
-- title:
--   Exponential product event section at fixed second coordinate
-- statement:
--   The mass of the truncated exponential event at fixed d equals the translated density integral, supported where x-y<d≤x.
-- source:
--   Kyprianou (2006), Corollary 8.8, exponential mixture.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_exponential_mixture_section :
    ∀ (φ x d : ℝ), 0 < φ → ∀ A : Set ℝ, MeasurableSet A →
      expMeasure φ {s : ℝ | d ≤ x ∧ x + s - d ∈ A} =
      ∫⁻ y in A, (if x-y < d ∧ d ≤ x then
        ENNReal.ofReal (φ * Real.exp (-φ * (y-x+d))) else 0) := by
  sorry
end Kyprianou.Ch08.StageB
