-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_density_pointwise_tendsto
-- name    : Kyprianou.Ch08.StageB.qzero_killed_density_pointwise_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:56:48.524731+00:00
-- url     : https://prove2.me/theorems/0936ec09-ba50-410f-bec0-276c6494a24e
-- title:
--   Conditional pointwise zero-discount convergence of the killed interval density
-- statement:
--   The killed density pointwise limit follows from strict positive-reserve denominator positivity, nonnegative-argument discount continuity, and negative-argument zero extension.
-- source:
--   Kyprianou (2006), Chapter 8, zero-discount killed interval occupation density.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology

namespace Kyprianou.Ch08.StageB

/-- Conditional pointwise zero-discount convergence of the killed interval density. -/
theorem qzero_killed_density_pointwise_tendsto :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ a : ℝ, 0 < a → 0 < W 0 a) →
    (∀ z : ℝ, 0 ≤ z →
      Tendsto (fun n : ℕ => W (((n : ℝ) + 1)⁻¹) z) atTop (𝓝 (W 0 z))) →
    (∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ y : ℝ, Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y)) atTop
        (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y))) := by
  sorry

end Kyprianou.Ch08.StageB
