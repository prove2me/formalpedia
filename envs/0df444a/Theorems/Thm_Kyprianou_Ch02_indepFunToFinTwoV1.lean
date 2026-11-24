-- Prove2me | Theorems.Thm_Kyprianou_Ch02_indepFunToFinTwoV1
-- name    : Kyprianou.Ch02.indepFunToFinTwoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:55:08.299801+00:00
-- url     : https://prove2.me/theorems/8bef59e4-1c92-4fcd-b094-91f1cc40891f
-- title:
--   Two independent variables form an independent Fin 2 family
-- statement:
--   Use the finite-family rectangle characterization, with empty, singleton, and full index sets.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.indepFunToFinTwoV1
    {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → β)
    (h : IndepFun A B P) :
    iIndepFun (fun (i : Fin 2) ω => if i=0 then A ω else B ω) P := by sorry
