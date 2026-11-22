-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:59:34.880764+00:00
-- url     : https://prove2.me/theorems/16dfa1ec-a384-4d1d-b03b-2eebea920728
-- title:
--   Theorem 8.1 upward exit before ruin
-- statement:
--   Identify the upward exit payoff with the scale ratio via survival and strong Markov at strict upward passage, with the Esscher change of measure for positive discount and a zero-discount limit when required.
-- source:
--   Kyprianou (2006), Chapter 8, (8.8), pp. 214–215. Decomposition of dd90765c-572a-4a22-9657-966e9544f3d3.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    upBeforeDownExpectation P D.X q x a = W q x / W q a := by
  sorry
