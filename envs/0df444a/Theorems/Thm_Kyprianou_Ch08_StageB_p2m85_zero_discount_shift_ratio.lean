-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_zero_discount_shift_ratio
-- name    : Kyprianou.Ch08.StageB.p2m85_zero_discount_shift_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:11:46.362182+00:00
-- url     : https://prove2.me/theorems/690d0fdf-9375-4ff7-b632-ba9358822072
-- title:
--   Zero-discount shifted scale ratio
-- statement:
--   Use Theorem 8.2 and the vanishing fixed-width excursion tail integral.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), zero-discount limits.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_zero_discount_shift_ratio
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) :
    Tendsto (fun a : ℝ => W 0 (a-x) / W 0 a)
      atTop (𝓝 (Real.exp (-Phi ψ 0 * x))) := by
  sorry
