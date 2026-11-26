-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42AvramIsLevyProcessV1
-- name    : Kyprianou.Ch04.exercise42AvramIsLevyProcessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:45:48.658811+00:00
-- url     : https://prove2.me/theorems/6d49afb9-3282-5a4b-9cee-a54fda4367ba
-- title:
--   Original Avram source is a LeanLevy process
-- statement:
--   The Avram spectrally negative Lévy source satisfies the LeanLevy process predicate on its original probability space.
-- source:
--   Supporting source-model interface for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise42AvramIndependentIncrementsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42AvramIsLevyProcessV1
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    IsLevyProcess L.X P := by
  sorry
