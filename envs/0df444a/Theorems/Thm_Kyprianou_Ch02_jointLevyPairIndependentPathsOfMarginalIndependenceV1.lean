-- Prove2me | Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentPathsOfMarginalIndependenceV1
-- name    : Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:55:07.551222+00:00
-- url     : https://prove2.me/theorems/7c6b362a-3ca5-470b-85b7-03163ca39a11
-- title:
--   Independent pair marginals and joint stationary independent increments yield independent paths
-- statement:
--   For any two finite time sets choose a common ordered grid starting at zero. Its two coordinate increment arrays are independent. Each path restriction is a measurable prefix-sum map of the respective array. Apply the finite-cylinder criterion.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P) :
    IndepFun (fun ω t => A t ω) (fun ω t => B t ω) P := by sorry
