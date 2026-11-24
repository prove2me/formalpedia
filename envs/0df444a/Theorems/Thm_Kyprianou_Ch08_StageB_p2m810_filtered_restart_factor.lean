-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_filtered_restart_factor
-- name    : Kyprianou.Ch08.StageB.p2m810_filtered_restart_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:00:33.652812+00:00
-- url     : https://prove2.me/theorems/fcc6893a-2be2-4688-9d8d-13d58dfbffb3
-- title:
--   Filtered model first-record regeneration factor
-- statement:
--   Apply the proved uncapped real stopped-reward factor at lower x-a and upper x. Identify the past weight and the future reward using the preceding source-exact lemmas.
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
/-- Filtered model first-record regeneration factor -/
theorem p2m810_filtered_restart_factor :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
      (X : SpectrallyNegativeLevy P F) (q x a l : ℝ), 0 ≤ q → 0 < a → 0 < x → x ≤ a → x < l →
      (∫ ω, if tauPlus X.X l ω < reflectedSupExit X.X x a ω
        then discountedAt q (tauPlus X.X l ω) else 0 ∂P) =
      upBeforeDownExpectation P X.X q (a-x) a *
      (∫ ω, if tauPlus X.X (l-x) ω < reflectedSupExit X.X 0 a ω
        then discountedAt q (tauPlus X.X (l-x) ω) else 0 ∂P) := by
  sorry
end Kyprianou.Ch08.StageB
