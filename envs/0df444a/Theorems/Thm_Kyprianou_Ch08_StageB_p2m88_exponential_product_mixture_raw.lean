-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_product_mixture_raw
-- name    : Kyprianou.Ch08.StageB.p2m88_exponential_product_mixture_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:10:49.829841+00:00
-- url     : https://prove2.me/theorems/fe69867f-3826-4337-ba9b-3c91180546c7
-- title:
--   Tonelli density of the truncated exponential product pushforward
-- statement:
--   The density of the sum of a positive-rate exponential factor and x minus an independent marginal truncated at x is the integral of the shifted exponential density over the half-open interval (x-y,x]. The density is measurable.
-- source:
--   Kyprianou (2006), Theorem 8.7, convolution of the two independent Wiener–Hopf factors.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Tonelli density of the truncated exponential product pushforward -/
theorem p2m88_exponential_product_mixture_raw :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ : ℝ), 0 < φ →
      ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A →
      let g : ℝ → ℝ≥0∞ := fun y =>
        ∫⁻ d in Ioc (x - y) x, ENNReal.ofReal (φ * Real.exp (-φ * (y - x + d))) ∂ν
      Measurable g ∧
        ((expMeasure φ).prod ν) {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} =
          ∫⁻ y in A, g y := by
  sorry

end Kyprianou.Ch08.StageB
