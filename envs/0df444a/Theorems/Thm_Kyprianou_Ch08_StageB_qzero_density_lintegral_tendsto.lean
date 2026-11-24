-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_qzero_density_lintegral_tendsto
-- name    : Kyprianou.Ch08.StageB.qzero_density_lintegral_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T00:58:25.943824+00:00
-- url     : https://prove2.me/theorems/e32d189f-3515-4504-a8a3-68f746e7711b
-- title:
--   Conditional density-side sequential limit
-- statement:
--   The density lintegral limit follows from the pointwise convergence and uniform dominant helper conclusions.
-- source:
--   Kyprianou (2006), Chapter 8, zero-discount killed interval occupation density.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology

namespace Kyprianou.Ch08.StageB

/-- Conditional density-side sequential limit for the zero-discount occupation identity. -/
theorem qzero_density_lintegral_tendsto :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ y : ℝ, Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y)) atTop
        (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y)))) →
    (∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y) ≤
        ENNReal.ofReal (W 1 x * W 1 a / W 0 a + W 1 x)) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        Tendsto
          (fun n : ℕ =>
            ((volume.restrict (Set.Icc 0 a)).withDensity
              (fun y : ℝ => ENNReal.ofReal
                (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y))) A)
          atTop
          (𝓝 (((volume.restrict (Set.Icc 0 a)).withDensity
            (fun y : ℝ => ENNReal.ofReal
              (killedIntervalDensity (W 0) a x y))) A)) := by
  sorry

end Kyprianou.Ch08.StageB
