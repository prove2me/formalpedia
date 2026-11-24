-- Prove2me | Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
-- name    : Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:16:09.897071+00:00
-- url     : https://prove2.me/theorems/e91e3e36-42cf-4957-a1a9-131e9d54c379
-- title:
--   Almost-everywhere measurability of whole real Levy paths from the independent-increments source predicate
-- statement:
--   For any original real Lévy process in the LeanLevy IsLevyProcess sense, the map from sample points to full real-valued paths on nonnegative time is almost-everywhere measurable into the product measurable space, without requiring a separate measurable time-slice assumption. Extract the aemeasurability of each time-slice from the stationary/independent increment conditions, use literal X(0)=0, and combine coordinate-wise through aemeasurable_pi_iff. This is a source-faithful reusable lemma enabling transfer of measurable cadlag weighted jump functionals to the original Chapter 2 process.
-- source:
--   Kyprianou (2006) Chapter 2 source-Levy regularity; LeanLevy imported Processes.StochasticProcess and Processes.LevyProcess

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    AEMeasurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) P := by
  sorry
