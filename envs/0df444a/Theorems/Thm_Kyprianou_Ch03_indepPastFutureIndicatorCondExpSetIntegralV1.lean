-- Prove2me | Theorems.Thm_Kyprianou_Ch03_indepPastFutureIndicatorCondExpSetIntegralV1
-- name    : Kyprianou.Ch03.indepPastFutureIndicatorCondExpSetIntegralV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:03:39.803435+00:00
-- url     : https://prove2.me/theorems/6a870581-0ee4-4990-b7cb-eb140983d7c6
-- title:
--   Past conditional indicator expectation has matching integrals on the past-future join
-- statement:
--   On rectangles B ∩ C with B past-measurable and C future-measurable, factor the two indicator integrals using independence of g and h, and use the defining property of conditional expectation on B. Extend the resulting equality to the generated join by finite signed-measure uniqueness or measurable-space pi-system induction.
-- source:
--   Kyprianou (2006), Exercise 3.1; parent 26506043-35dd-48b6-a6a6-e3a4be846eae.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.indepPastFutureIndicatorCondExpSetIntegralV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h) (hjoin : m ⊔ h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (A : Set Omega) (hA : MeasurableSet[g] A) :
    ∀ S : Set Omega, MeasurableSet[m ⊔ h] S →
      (∫ x in S, (P[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂P) =
        ∫ x in S, A.indicator (fun _ => (1 : ℝ)) x ∂P := by
  sorry
