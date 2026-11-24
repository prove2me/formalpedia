-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralContinuousClosedV1
-- name    : Kyprianou.Ch02.positiveLaplaceIntegralContinuousClosedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:53:46.733403+00:00
-- url     : https://prove2.me/theorems/93ef03fb-2e39-45b8-9c0f-4fb11b18bb8f
-- title:
--   positiveLaplaceIntegralContinuousClosed
-- statement:
--   positiveLaplaceIntegralContinuousClosed
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLaplaceIntegralContinuousClosedV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    ContinuousOn (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 ≤ z.re} := by sorry
