-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralDifferentiableV1
-- name    : Kyprianou.Ch02.positiveLaplaceIntegralDifferentiableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:53:45.160725+00:00
-- url     : https://prove2.me/theorems/ddb90bbb-53d9-4630-8ee2-3c7f8f731221
-- title:
--   positiveLaplaceIntegralDifferentiable
-- statement:
--   positiveLaplaceIntegralDifferentiable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLaplaceIntegralDifferentiableV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 < z.re} := by sorry
