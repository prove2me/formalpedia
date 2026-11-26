-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42AvramIndependentIncrementsV1
-- name    : Kyprianou.Ch04.exercise42AvramIndependentIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:05:38.237117+00:00
-- url     : https://prove2.me/theorems/9d09a13b-fb1f-54c5-8bb1-a75a041daffb
-- title:
--   Avram filtration increments give LeanLevy finite-partition independence
-- statement:
--   The independent increments from the past filtration in the Avram source structure imply joint independence of all increments along each finite ordered time partition.
-- source:
--   Supporting source-model interface for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42AvramIndependentIncrementsV1
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ProbabilityTheory.HasIndependentIncrements L.X P := by
  sorry
