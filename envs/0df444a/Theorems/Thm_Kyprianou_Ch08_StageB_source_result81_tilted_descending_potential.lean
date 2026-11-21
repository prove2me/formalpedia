-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_descending_potential
-- name    : Kyprianou.Ch08.StageB.source_result81_tilted_descending_potential
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:40:00.650818+00:00
-- url     : https://prove2.me/theorems/4c63d0ad-20de-450a-9ecd-09b666951d4c
-- title:
--   Tilted descending potential for the scale-function transform
-- statement:
--   The descending potential at the right Esscher root is supported on the nonnegative half-line and has no positive-location atoms. Its exponential transform is the reciprocal of the shifted descending renewal exponent. An atom at the origin is allowed.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful decomposition of b5430c32-5738-4ad5-9956-e8891a1d6407.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_tilted_descending_potential
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)))
    (q : ℝ) (hq : 0 ≤ q) :
    IsScaleTransformDomainBridge A.ψ q ∧
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ x : ℝ, 0 < x → ν {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / (A.ψ (Phi A.ψ q + s) - q))) := by
  sorry
