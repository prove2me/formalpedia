-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralDiffContOnClV1
-- name    : Kyprianou.Ch02.positiveLaplaceIntegralDiffContOnClV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:49:45.262796+00:00
-- url     : https://prove2.me/theorems/d3e3c294-aa2f-4e58-946c-29a06e850cf3
-- title:
--   positiveLaplaceIntegralDiffContOnCl
-- statement:
--   positiveLaplaceIntegralDiffContOnCl
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLaplaceIntegralDiffContOnClV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    DiffContOnCl ℂ (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 < z.re} := by sorry
