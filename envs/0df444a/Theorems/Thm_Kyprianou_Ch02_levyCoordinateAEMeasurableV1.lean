-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
-- name    : Kyprianou.Ch02.levyCoordinateAEMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:20:41.935839+00:00
-- url     : https://prove2.me/theorems/b612c989-54bb-455d-8291-ca7b306b23e5
-- title:
--   Original real Levy time-slice a.e. measurability from source independent/stationary increments
-- statement:
--   Prove that any real IsLevyProcess process has almost everywhere measurable evaluation at each fixed time. Extract AEMeasurable of the source zero-start increment from its stationary-increment IdentDistrib witness and rewrite using literal source start_zero. This supplies a genuine measurable time-slice premise for cadlag path regularisation.
-- source:
--   Kyprianou (2006) Chapter 2 source-Levy regularity; LeanLevy imported Processes.StochasticProcess and Processes.LevyProcess

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyCoordinateAEMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    ∀ t : ℝ≥0, AEMeasurable (X t) P := by
  sorry
