-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49SpikeTimeV3
-- name    : Kyprianou.Ch04.exercise49SpikeTimeV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:48:57.271437+00:00
-- url     : https://prove2.me/theorems/75dddd7f-6d56-501f-b353-75b619be67f8
-- title:
--   A path negative only at one strictly positive instant has that instant as its first strict downward entrance
-- statement:
--   A path negative only at one strictly positive instant has that instant as its first strict downward entrance
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), exceptional-path statement audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49SpikeTimeV3
    (a : NNReal) (ha : 0 < a) :
    sInf {v : WithTop NNReal | ∃ t : NNReal, v = ↑t ∧ 0 < t ∧
      (if t = a then (-1 : ℝ) else 0) < 0} = (a : WithTop NNReal) := by
  sorry
