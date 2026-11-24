-- Prove2me | Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralRealNonnegV1
-- name    : Kyprianou.Ch02.positiveLaplaceIntegralRealNonnegV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:49:45.91801+00:00
-- url     : https://prove2.me/theorems/1a25981a-5596-4eda-aefc-acd8b9605dbf
-- title:
--   positiveLaplaceIntegralRealNonneg
-- statement:
--   positiveLaplaceIntegralRealNonneg
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.positiveLaplaceIntegralRealNonnegV1
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ (∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν).re := by sorry
