-- Prove2me | Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentGridIncrementsV1
-- name    : Kyprianou.Ch02.jointLevyPairIndependentGridIncrementsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:55:06.428331+00:00
-- url     : https://prove2.me/theorems/fe88d011-35fa-4c79-b40c-fa2d0432a3e5
-- title:
--   Independent coordinates of every pair marginal imply independent coordinate increment arrays
-- statement:
--   Each pair increment is distributed as its pair marginal at the elapsed time. Apply the independent pair-array lemma to the independent increments.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.jointLevyPairIndependentGridIncrementsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℝ≥0 → Ω → ℝ)
    (hA0 : A 0 = fun _ => 0) (hB0 : B 0 = fun _ => 0)
    (hmA : ∀ t, AEMeasurable (A t) P) (hmB : ∀ t, AEMeasurable (B t) P)
    (hi : HasIndependentIncrements (fun t ω => (A t ω,B t ω)) P)
    (hs : HasStationaryIncrements (fun t ω => (A t ω,B t ω)) P)
    (hc : ∀ t, IndepFun (A t) (B t) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    IndepFun (fun ω (i : Fin n) => A (t i.succ) ω-A (t i.castSucc) ω)
      (fun ω (i : Fin n) => B (t i.succ) ω-B (t i.castSucc) ω) P := by sorry
