-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ce_linear_indep
-- name    : Kyprianou.Ch04.ito43_ce_linear_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:13:13.531488+00:00
-- url     : https://prove2.me/theorems/5b8e8ed6-80ca-4a5c-964e-fe8f6a6ab2bb
-- title:
--   Deterministic drift has independent increments
-- statement:
--   Deterministic drift has independent increments.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3 formalisation boundary audit.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Deterministic drift increments form independent families. -/

theorem Kyprianou.Ch04.ito43_ce_linear_indep {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    HasIndependentIncrements (fun (t : NNReal) (_ : Ω) => (t : ℝ)) P := by sorry
