-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_inverse_slope_limit
-- name    : Kyprianou.Ch08.StageB.p2m89_inverse_slope_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:21.580657+00:00
-- url     : https://prove2.me/theorems/7a4753d9-abe7-4948-aab7-72d44a70169f
-- title:
--   Positive root reciprocal slope limit
-- statement:
--   Differentiability at the positive root identifies the inverse slope limit.
-- source:
--   Reduction of 7b5acc12-33ec-419f-a633-a7295bab46be.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_inverse_slope_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ((n : ℝ) + 1)) /
      (ψ (Phi ψ q + 1 / ((n : ℝ) + 1)) - q))) atTop
      (𝓝 (ENNReal.ofReal (deriv (Phi ψ) q))) := by
  sorry
