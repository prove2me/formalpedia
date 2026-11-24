-- Prove2me | Theorems.Thm_Kyprianou_Ch03_indepPastFutureJoinEventExactAmbientV1
-- name    : Kyprianou.Ch03.indepPastFutureJoinEventExactAmbientV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:31:15.251623+00:00
-- url     : https://prove2.me/theorems/26506043-35dd-48b6-a6a6-e3a4be846eae
-- title:
--   Independent intermediate sigma-algebra events have an exact past representative modulo null sets
-- statement:
--   Ambient-measurable form of the independent intermediate sigma-algebra lemma. Take the conditional expectation of the indicator of A given m. Independence of g and h gives agreement of its integral with the indicator on every rectangle C∩D with C in m and D in h. Use finite-measure uniqueness on the rectangle pi-system generating m∨h. Both functions are measurable on m∨h, so they agree almost everywhere. Threshold the conditional expectation at 1/2. The outer-null-measurable version follows by applying this result under the completion of the original measure.
-- source:
--   Measure-theoretic helper for Kyprianou Chapter 3 Exercise 3.1, c6f4e98a-56cd-4b9b-9d46-ff0a78fc4188.

import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.indepPastFutureJoinEventExactAmbientV1
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (m g h : MeasurableSpace Omega)
    (hmg : m ≤ g) (hgh : g ≤ m ⊔ h) (hjoin : m ⊔ h ≤ mΩ)
    (hInd : @Indep Omega g h mΩ P)
    (A : Set Omega) (hA : MeasurableSet[g] A) :
    ∃ B : Set Omega, MeasurableSet[m] B ∧ P ((A \ B) ∪ (B \ A)) = 0 := by
  sorry
