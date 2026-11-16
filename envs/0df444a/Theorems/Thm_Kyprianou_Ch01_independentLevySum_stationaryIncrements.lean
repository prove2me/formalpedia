-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentLevySum_stationaryIncrements
-- name    : Kyprianou.Ch01.independentLevySum_stationaryIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:33:47.34242+00:00
-- url     : https://prove2.me/theorems/faa196ca-76a5-4ac7-9cfc-82fd050c9796
-- title:
--   Stationary increments of the sum of two independent Levy processes
-- statement:
--   The increment law of the sum of two independent Levy processes depends only on the time lag, because each constituent has stationary increments and the processes are independent.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.1, original target 1de56fa3-80d8-45c5-84de-bac5401cda86; original LeanLevy IsLevyProcess structure fields.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentLevySum_stationaryIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hY : IsLevyProcess Y P)
    (hXY : IndepFun (fun ω => fun t => X t ω)
      (fun ω => fun t => Y t ω) P) :
    HasStationaryIncrements (fun t ω => X t ω + Y t ω) P := by sorry
