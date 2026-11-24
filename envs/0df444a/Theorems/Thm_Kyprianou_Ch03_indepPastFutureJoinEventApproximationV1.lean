-- Prove2me | Theorems.Thm_Kyprianou_Ch03_indepPastFutureJoinEventApproximationV1
-- name    : Kyprianou.Ch03.indepPastFutureJoinEventApproximationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:28:05.840803+00:00
-- url     : https://prove2.me/theorems/c6f4e98a-56cd-4b9b-9d46-ff0a78fc4188
-- title:
--   Independent intermediate sigma-algebra events are approximable by past events
-- statement:
--   An abstract probability lemma: if a sigma-algebra g contains m, is contained in m joined with h, and is independent of h, then every g-event agrees almost surely with an m-event, assuming the join consists of ambient null-measurable sets. Work under the completion of P, take conditional expectation of the event indicator on m, and test on rectangles C∩D where C belongs to m and D belongs to h. Since the indicator and the conditional expectation are g-measurable and h is independent of g, the integrals agree on every rectangle. Extend by finite-measure uniqueness to m∨h. Both functions are measurable for this join, so equality holds a.e.; threshold the conditional expectation. No raw sigma-algebra need be contained in the uncompleted ambient space.
-- source:
--   Kyprianou (2006), Exercise 3.1; parent dc6deda8-897b-4e0f-b4f3-f2428ced614a.

import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.indepPastFutureJoinEventApproximationV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h)
    (hInd : @Indep Omega g h mΩ P)
    (hNull : ∀ S : Set Omega, MeasurableSet[m ⊔ h] S → @NullMeasurableSet Omega mΩ S P)
    (A : Set Omega) (hA : MeasurableSet[g] A)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ B : Set Omega, MeasurableSet[m] B ∧ P ((A \ B) ∪ (B \ A)) < ε := by
  sorry
