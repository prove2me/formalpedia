-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_discount_z_ratio
-- name    : Kyprianou.Ch08.StageB.p2m85_positive_discount_z_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T15:13:50.167275+00:00
-- url     : https://prove2.me/theorems/e5e02b52-c1c5-4647-a82c-06a5fa1e4512
-- title:
--   Positive-discount integrated Z-scale ratio at infinity
-- statement:
--   Apply the tilted scale limit and exponential convolution identity to numerator and denominator.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), positive discount asymptotic.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.p2m85_positive_discount_z_ratio
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    Tendsto (fun z : ℝ => Zscale q (W q) z / W q z)
      atTop (𝓝 (q / Phi ψ q)) := by
  sorry
