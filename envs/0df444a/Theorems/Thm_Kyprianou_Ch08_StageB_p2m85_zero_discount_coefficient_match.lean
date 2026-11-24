-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_discount_coefficient_match
-- name    : Kyprianou.Ch08.StageB.p2m85_zero_discount_coefficient_match
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:11:27.204993+00:00
-- url     : https://prove2.me/theorems/f1ba2ad0-aac3-4170-a1c3-bcb184b3a9c4
-- title:
--   Zero-discount quotient coefficient and reciprocal scale limit
-- statement:
--   Identify the common zero-discount coefficient and limit of the reciprocal zero-scale function.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), zero-discount limits.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_zero_discount_coefficient_match
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) :
    ∃ c : ℝ,
      Tendsto (fun q : ℝ => q / Phi ψ q) (nhdsWithin 0 (Ioi 0)) (𝓝 c) ∧
      Tendsto (fun z : ℝ => Zscale 0 (W 0) z / W 0 z) atTop (𝓝 c) := by
  sorry
