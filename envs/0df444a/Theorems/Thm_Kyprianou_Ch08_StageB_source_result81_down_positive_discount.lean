-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_down_positive_discount
-- name    : Kyprianou.Ch08.StageB.source_result81_down_positive_discount
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T13:20:08.81071+00:00
-- url     : https://prove2.me/theorems/d5833b96-248c-4b9d-87b8-3cb8b121acb0
-- title:
--   One-sided ruin at positive discount
-- statement:
--   Identify the infimum at an independent rate-q exponential time using Wiener–Hopf, and identify its distribution function by the Laplace transform of the known scale family. The event of downward passage before killing supplies the positive-discount payoff.
-- source:
--   Kyprianou (2006), Chapter 8, equations (8.6)–(8.7), pp. 214–215. Decomposition of 8f95e53d-1cfe-4e26-a9c2-0fa1c54631b2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_down_positive_discount
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 < q) :
    downExpectation P D.X q x =
      Zscale q (W q) x - q / Phi ψ q * W q x := by
  sorry
