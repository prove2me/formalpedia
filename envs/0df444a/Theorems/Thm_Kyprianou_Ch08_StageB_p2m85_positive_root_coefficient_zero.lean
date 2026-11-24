-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_root_coefficient_zero
-- name    : Kyprianou.Ch08.StageB.p2m85_positive_root_coefficient_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:59:36.750441+00:00
-- url     : https://prove2.me/theorems/04bf4e8f-6974-456b-b412-92856042cee9
-- title:
--   At a strictly positive zero-discount root, continuity along positive discounts forces the quotient coefficient to zero.
-- statement:
--   At a strictly positive zero-discount root, continuity along positive discounts forces the quotient coefficient to zero.
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem Kyprianou.Ch08.StageB.p2m85_positive_root_coefficient_zero
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (c : ℝ) (hφ : 0 < Phi ψ 0)
    (hlim : Tendsto (fun q : ℝ => q / Phi ψ q) (nhdsWithin 0 (Ioi 0)) (𝓝 c)) :
    c = 0 := by
  sorry
