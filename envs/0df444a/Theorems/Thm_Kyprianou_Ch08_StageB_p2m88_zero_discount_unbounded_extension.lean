-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_zero_discount_unbounded_extension
-- name    : Kyprianou.Ch08.StageB.p2m88_zero_discount_unbounded_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:43:08.162437+00:00
-- url     : https://prove2.me/theorems/d3b3886c-ae50-49c0-8e4c-24c5b68288ad
-- title:
--   Extend zero-discount occupation from bounded terminal sets
-- statement:
--   The terminal sets intersected with increasing upper cutoffs exhaust the original set. Measure continuity from below and monotone convergence of the measurable time-section probabilities extend the bounded identity to arbitrary Borel terminal sets.
-- source:
--   Kyprianou (2006), Corollary 8.8, zero-discount limit.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_zero_discount_unbounded_extension :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W → ∀ x : ℝ, 0 ≤ x →
      ∀ A : Set ℝ, MeasurableSet A →
      (∀ n : ℕ, ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) (A ∩ Iic (n : ℝ)) =
        ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          shifted D.X x t ω ∈ A ∩ Iic (n : ℝ)} ∂positiveTimeLebesgue) →
      ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A =
      ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry
end Kyprianou.Ch08.StageB
