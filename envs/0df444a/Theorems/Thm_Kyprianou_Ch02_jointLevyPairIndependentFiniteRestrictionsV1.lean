-- Prove2me | Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentFiniteRestrictionsV1
-- name    : Kyprianou.Ch02.jointLevyPairIndependentFiniteRestrictionsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:22:46.757471+00:00
-- url     : https://prove2.me/theorems/a8d1b8f6-86c6-42ea-8995-7e87e4df6aaa
-- title:
--   Independent marginals and joint independent increments imply independent finite restrictions
-- statement:
--   Sort the union of the two finite time sets together with zero. Joint increments on consecutive intervals are independent, and stationarity gives within-interval independence of their two coordinates. The two full vectors of coordinate increments are independent by the product law. Finite cumulative values are measurable functions of the respective vectors.
-- source:
--   Kyprianou (2006), Exercise 2.8; finite-dimensional independence

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.jointLevyPairIndependentFiniteRestrictionsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P) :
    ∀ I J : Finset ℝ≥0,
      IndepFun (fun ω (i : I) => A i ω) (fun ω (j : J) => B j ω) P := by
  sorry
