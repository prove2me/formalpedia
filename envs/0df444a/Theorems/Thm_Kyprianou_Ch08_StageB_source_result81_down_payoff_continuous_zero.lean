-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_down_payoff_continuous_zero
-- name    : Kyprianou.Ch08.StageB.source_result81_down_payoff_continuous_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:20:12.995883+00:00
-- url     : https://prove2.me/theorems/e19453fb-5e84-48e4-9cb4-e9ad497b4a66
-- title:
--   Downward discounted payoff converges to ruin probability
-- statement:
--   Use almost-everywhere measurability of the downward clock established by rational-time strict crossings on càdlàg paths. Discount converges to the finite-clock indicator and is dominated by one.
-- source:
--   Kyprianou (2006), Chapter 8, equations (8.6)–(8.7), pp. 214–215. Decomposition of 8f95e53d-1cfe-4e26-a9c2-0fa1c54631b2.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_down_payoff_continuous_zero
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (x : ℝ) :
    Tendsto (fun q : ℝ => downExpectation P D.X q x)
      (nhdsWithin 0 (Ioi 0)) (nhds (downExpectation P D.X 0 x)) := by
  sorry
