-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_avram_down_clock_stopping
-- name    : Kyprianou.Ch08.StageB.p2m810_avram_down_clock_stopping
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:08:28.505994+00:00
-- url     : https://prove2.me/theorems/6c65a379-7fd1-4509-8948-1093a8857cfe
-- title:
--   Identify the source strict downcrossing clock with the Avram lower-exit clock and apply its proved right-continuous-filtration stopping-time property.
-- statement:
--   Identify the source strict downcrossing clock with the Avram lower-exit clock and apply its proved right-continuous-filtration stopping-time property.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Probability.Process.Stopping
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_avram_down_clock_stopping
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F) (y : ℝ) :
    MeasureTheory.IsStoppingTime F.rightCont (tauMinus (shifted X.X y) 0) := by
  sorry
