-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49AddLinearLevyV4
-- name    : Kyprianou.Ch04.exercise49AddLinearLevyV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:01:50.420225+00:00
-- url     : https://prove2.me/theorems/80df6c93-9f33-4a11-a728-bbb79f4a0dbb
-- title:
--   exercise49AddLinearLevyV4
-- statement:
--   exercise49AddLinearLevyV4
-- source:
--   Exercise 4.9(iii) admissible model construction

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]

theorem Kyprianou.Ch04.exercise49AddLinearLevyV4 (P : Measure Ω) (Z : NNReal → Ω → ℝ) (hZ : IsLevyProcess Z P) (b : ℝ) :
    IsLevyProcess (fun t w => Z t w + b * (t : ℝ)) P := by sorry
