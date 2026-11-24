-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_product_mixture_density
-- name    : Kyprianou.Ch08.StageB.p2m88_exponential_product_mixture_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:00:59.562866+00:00
-- url     : https://prove2.me/theorems/3ae07932-5e69-4e91-b215-84e8d5e888c2
-- title:
--   Independent exponential and truncated marginal mixture density
-- statement:
--   For any real probability law and an independent positive-rate exponential, truncate the second coordinate at x and push forward by x plus the first coordinate minus the second. The discounted product event equals the Lebesgue integral of the exponential factor times the exponentially weighted half-open interval mass.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7 and Corollary 8.8, integration by parts in the exponential-clock law.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Independent exponential and truncated marginal mixture density -/
theorem p2m88_exponential_product_mixture_density :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ), 0 < φ → 0 < q →
      ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A →
      (ENNReal.ofReal q)⁻¹ * ((expMeasure φ).prod ν)
        {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} =
      ∫⁻ y in A, (ENNReal.ofReal (φ / q * Real.exp (-φ * (y - x)))) *
        (∫⁻ z in Ioc (x - y) x, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν)
        ∂(volume.restrict (Ici (0 : ℝ))) := by
  sorry

end Kyprianou.Ch08.StageB
