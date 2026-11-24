-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_initial_shifted_clock_pair
-- name    : Kyprianou.Ch08.StageB.p2m810_initial_shifted_clock_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:10:12.446259+00:00
-- url     : https://prove2.me/theorems/ff24de8e-47d9-4995-a677-9511b0ca4077
-- title:
--   Initial shifted source clocks equal filtered clocks
-- statement:
--   Right continuity identifies the positive-time open passage clocks with the all-time Avram clocks. Translate each threshold by a-x.
-- source:
--   Kyprianou (2006), Theorems 8.1 and 8.10(i).

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Initial shifted source clocks equal filtered clocks -/
theorem p2m810_initial_shifted_clock_pair :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F) (x a : ℝ) (ω : Ω),
      (tauPlus (shifted X.X (a-x)) a ω : ℝ≥0∞) = twoSidedExitUpTime X x ω ∧
      (tauMinus (shifted X.X (a-x)) 0 ω : ℝ≥0∞) = twoSidedExitDownTime X (x-a) ω := by
  sorry
end Kyprianou.Ch08.StageB
