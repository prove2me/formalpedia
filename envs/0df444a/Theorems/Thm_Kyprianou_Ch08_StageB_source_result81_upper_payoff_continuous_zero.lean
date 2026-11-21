-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_continuous_zero
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_payoff_continuous_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:40:12.620173+00:00
-- url     : https://prove2.me/theorems/56d28aed-aec3-4761-b4d8-75594524f739
-- title:
--   The upward-first payoff converges as discount tends to zero
-- statement:
--   Use rational-time representations of the two strict passage clocks to get almost-everywhere measurability of their ordering, then apply dominated convergence to the discounted upward clock with this fixed event.
-- source:
--   Kyprianou (2006), Chapter 8, equation (8.8), pp. 214–215. Decomposition of 16dfa1ec-a384-4d1d-b03b-2eebea920728.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_payoff_continuous_zero
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (x a : ℝ) :
    Tendsto (fun q : ℝ => upBeforeDownExpectation P D.X q x a)
      (nhdsWithin 0 (Ioi 0)) (nhds (upBeforeDownExpectation P D.X 0 x a)) := by
  sorry
