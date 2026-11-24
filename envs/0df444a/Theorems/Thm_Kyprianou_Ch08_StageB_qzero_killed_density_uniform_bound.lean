-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_density_uniform_bound
-- name    : Kyprianou.Ch08.StageB.qzero_killed_density_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:58:24.423146+00:00
-- url     : https://prove2.me/theorems/732d9eab-c49b-4af0-8153-d8e87ab9e048
-- title:
--   Conditional uniform dominant for the killed interval density
-- statement:
--   The killed density dominant follows from the ratio bound, discount monotonicity and negative-argument zero extension.
-- source:
--   Kyprianou (2006), Chapter 8, zero-discount killed interval occupation density.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology

namespace Kyprianou.Ch08.StageB

/-- Conditional uniform dominant for the killed interval density. -/
theorem qzero_killed_density_uniform_bound :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ a : ℝ, 0 < a → 0 < W 0 a) →
    (∀ {r s z : ℝ}, 0 ≤ r → 0 ≤ s → r ≤ s → 0 ≤ z → W r z ≤ W s z) →
    (∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0) →
    (∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        W (((n : ℝ) + 1)⁻¹) x * W (((n : ℝ) + 1)⁻¹) (a - y) /
            W (((n : ℝ) + 1)⁻¹) a
          ≤ W 1 x * W 1 a / W 0 a) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y) ≤
        ENNReal.ofReal (W 1 x * W 1 a / W 0 a + W 1 x) := by
  sorry

end Kyprianou.Ch08.StageB
