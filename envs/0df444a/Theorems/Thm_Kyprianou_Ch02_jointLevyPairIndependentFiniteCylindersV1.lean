-- Prove2me | Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentFiniteCylindersV1
-- name    : Kyprianou.Ch02.jointLevyPairIndependentFiniteCylindersV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:54.827202+00:00
-- url     : https://prove2.me/theorems/07ad0964-80dd-4cef-a369-9924dad3369d
-- title:
--   Joint Levy coordinate finite cylinders are independent
-- statement:
--   Take an ordered grid covering the union of the two finite sets, prepend zero, and select the requested coordinates from the independent grid value arrays.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.jointLevyPairIndependentFiniteCylindersV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P)
    (I J : Finset ℝ≥0) :
    IndepFun (fun ω (i : I) => A i ω) (fun ω (j : J) => B j ω) P := by sorry
