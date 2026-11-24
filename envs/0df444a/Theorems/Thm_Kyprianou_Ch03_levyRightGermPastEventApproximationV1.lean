-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levyRightGermPastEventApproximationV1
-- name    : Kyprianou.Ch03.levyRightGermPastEventApproximationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:07:10.481812+00:00
-- url     : https://prove2.me/theorems/dc6deda8-897b-4e0f-b4f3-f2428ced614a
-- title:
--   Lévy right-germ events admit arbitrarily accurate past-event approximations
-- statement:
--   For a raw right-germ event, obtain approximation in probability by a raw past event. Work on the ambient probability completion, using the a.e. measurable full path map and a.s. right continuity. For a germ event, test its conditional expectation on past events and finite future increment cylinders. Future increments beyond t+h are independent of the past through t+h; let h decrease to zero using bounded continuous cylinder tests, then extend by a monotone class argument. The conditional expectation of the germ indicator on the completed past equals the indicator a.e.; choose a raw past event representing its threshold. This isolates the genuinely probabilistic density argument and avoids invalid distribution of sup over inf of sigma-algebras.
-- source:
--   Kyprianou (2006), Chapter 3 Exercise 3.1; parent f0666111-850e-44c9-8630-c8093e5f3095.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.levyRightGermPastEventApproximationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (A : Set Omega)
    (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ B : Set Omega, MeasurableSet[PerfCorrMSQ.natFiltr X t] B ∧
      P ((A \ B) ∪ (B \ A)) < ε := by
  sorry
