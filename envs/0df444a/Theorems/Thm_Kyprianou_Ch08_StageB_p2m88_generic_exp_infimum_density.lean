-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_generic_exp_infimum_density
-- name    : Kyprianou.Ch08.StageB.p2m88_generic_exp_infimum_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:43:11.453974+00:00
-- url     : https://prove2.me/theorems/0a44eb0c-9542-4346-988f-d24504dc2deb
-- title:
--   Exponential and infimum CDF mixture yields the half-line density
-- statement:
--   For any probability law on the nonnegative half-line whose CDF equals q/phi times a continuous nonnegative scale candidate less q times its primitive, the independent rate-phi exponential factor and negative-infimum factor, truncated at starting level x, have the stated discounted Lebesgue density on the half-line.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, equations (8.20), (8.28), Corollary 8.8; printed pp. 224–226.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Exponential and infimum CDF mixture yields the half-line density -/
theorem p2m88_generic_exp_infimum_density :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ) (w : ℝ → ℝ), 0 < φ → 0 < q → ν (Iio 0) = 0 →
      (∀ z : ℝ, z < 0 → w z = 0) →
      (∀ z : ℝ, 0 ≤ w z) →
      ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → cdf ν b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
        ((volume.restrict (Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (Real.exp (-φ * y) * w x - w (x - y)))) A =
        (ENNReal.ofReal q)⁻¹ * ((expMeasure φ).prod ν)
          {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} := by
  sorry

end Kyprianou.Ch08.StageB
