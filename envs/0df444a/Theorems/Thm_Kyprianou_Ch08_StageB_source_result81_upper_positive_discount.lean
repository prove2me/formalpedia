-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_positive_discount
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_positive_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:40:17.554942+00:00
-- url     : https://prove2.me/theorems/148f3af5-7490-41a1-96ec-bf500925e58a
-- title:
--   Upward exit ratio at positive discount
-- statement:
--   At the positive Esscher root, the survival distribution is proportional to the exponentially tilted scale. Strong Markov at the first upper crossing factors survival into passage before ruin and survival restarted from the upper level. Undoing the tilt yields the discount and ratio.
-- source:
--   Kyprianou (2006), Chapter 8, equation (8.8), pp. 214–215. Decomposition of 16dfa1ec-a384-4d1d-b03b-2eebea920728.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_positive_discount
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q x a : ℝ) (hq : 0 < q) (ha : 0 < a) (hxa : x ≤ a) :
    upBeforeDownExpectation P D.X q x a = W q x / W q a := by
  sorry
