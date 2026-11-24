-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_source_lower_clock_eq
-- name    : Kyprianou.Ch08.StageB.p2m88_avram_source_lower_clock_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:02:22.104945+00:00
-- url     : https://prove2.me/theorems/2aff1f29-9fde-45fe-a83c-3817219d8c57
-- title:
--   Source lower-passage clock equals Avram all-time exit clock
-- statement:
--   For the Avram right-continuous process, the positive-time shifted strict lower passage clock agrees pathwise with its all-time strict lower exit clock.
-- source:
--   Kyprianou (2006), Theorem 8.7, independent exponential-clock killing.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Source lower-passage clock equals Avram all-time exit clock -/
theorem p2m88_avram_source_lower_clock_eq :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
      (x : ℝ) (ω : Ω),
      (tauMinus (shifted X.X x) 0 ω : ℝ≥0∞) =
        AvramDividend.Classical.twoSidedExitDownTime X (-x) ω := by
  sorry

end Kyprianou.Ch08.StageB
