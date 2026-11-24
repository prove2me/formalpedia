-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_record_weight
-- name    : Kyprianou.Ch08.StageB.p2m810_filtered_record_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:00:34.684847+00:00
-- url     : https://prove2.me/theorems/dc4c24dd-58cc-43ff-84c8-8c69f2150d74
-- title:
--   Initial stopped record weight equals the two-sided exit expectation
-- statement:
--   The upper and lower Avram clocks are the raw strict clocks of the shifted source process with initial surplus a-x. Strict order makes the upper clock finite. At a finite upper clock the discount equals the real exponential.
-- source:
--   Kyprianou (2006), Theorem 8.10(i), strong Markov record regeneration.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
/-- Initial stopped record weight equals the two-sided exit expectation -/
theorem p2m810_filtered_record_weight :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a : ℝ),
      0 ≤ q → 0 < x → x ≤ a →
      (∫ ω, if twoSidedExitUpTime X x ω < twoSidedExitDownTime X (x-a) ω
        then Real.exp (-q*((twoSidedExitUpTime X x ω).toNNReal:ℝ)) else 0 ∂P) =
      upBeforeDownExpectation P X.X q (a-x) a := by
  sorry
end Kyprianou.Ch08.StageB
