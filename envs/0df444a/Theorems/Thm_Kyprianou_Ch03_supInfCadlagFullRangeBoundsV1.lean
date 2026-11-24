-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfCadlagFullRangeBoundsV1
-- name    : Kyprianou.Ch03.supInfCadlagFullRangeBoundsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:38.905315+00:00
-- url     : https://prove2.me/theorems/dd5eea50-c662-442d-a44c-818d8b97295a
-- title:
--   Both bounds of a càdlàg path on a finite horizon
-- statement:
--   Apply the proved càdlàg upper bound to f and its negative, which is also càdlàg, then transfer the negative upper bound to a lower bound.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; parent 595bcca9-772a-41a6-8165-d1d8abc9d6e8.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfCadlagFullRangeBoundsV1
    (f : NNReal → Real) (hf : IsCadlag f) (t : NNReal) :
    BddAbove (f '' Set.Icc 0 t) ∧ BddBelow (f '' Set.Icc 0 t) := by sorry
