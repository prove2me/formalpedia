-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_zero_discount_bounded_occupation
-- name    : Kyprianou.Ch08.StageB.p2m88_zero_discount_bounded_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:41:37.765546+00:00
-- url     : https://prove2.me/theorems/d9d4047a-f084-4f8f-8d17-05b9143dcb04
-- title:
--   Zero-discount occupation on bounded measurable terminal sets
-- statement:
--   Take the limit of the positive-discount identity along the reciprocal integer discount sequence, using dominated convergence on the bounded spatial set and monotone convergence on time.
-- source:
--   Kyprianou (2006), Corollary 8.8, zero-discount limit.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_zero_discount_bounded_occupation :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W → ∀ x : ℝ, 0 ≤ x →
      ∀ B : ℝ, 0 ≤ B → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Iic B →
      ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A =
      ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  sorry
end Kyprianou.Ch08.StageB
