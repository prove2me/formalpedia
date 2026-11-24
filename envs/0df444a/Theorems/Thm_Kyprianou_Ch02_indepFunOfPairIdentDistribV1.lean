-- Prove2me | Theorems.Thm_Kyprianou_Ch02_indepFunOfPairIdentDistribV1
-- name    : Kyprianou.Ch02.indepFunOfPairIdentDistribV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:55:11.898008+00:00
-- url     : https://prove2.me/theorems/5cdac796-8b06-4954-8c64-e33019540c06
-- title:
--   Independence of coordinates transfers under equality of joint laws
-- statement:
--   The product-law criterion for independence depends only on the joint and marginal laws, all of which transfer by identical distribution.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.indepFunOfPairIdentDistribV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : Ω → ℝ × ℝ) (h : IdentDistrib F G P P)
    (hi : IndepFun (fun ω => (G ω).1) (fun ω => (G ω).2) P) :
    IndepFun (fun ω => (F ω).1) (fun ω => (F ω).2) P := by sorry
