-- Prove2me | Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentGridValuesV1
-- name    : Kyprianou.Ch02.jointLevyPairIndependentGridValuesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:21:54.017919+00:00
-- url     : https://prove2.me/theorems/7cead197-3069-4c77-b3b6-d25db1714036
-- title:
--   Independent joint Levy coordinate grid values
-- statement:
--   Stationarity and independence of the coordinates at each time imply independence of the two coordinates of each deterministic increment pair. Independence of the increment pairs yields independence of their projected arrays. Measurable prefix sums reconstruct each grid value from its own array.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.jointLevyPairIndependentGridValuesV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) :
    IndepFun (fun ω i => A (t i) ω) (fun ω i => B (t i) ω) P := by sorry
