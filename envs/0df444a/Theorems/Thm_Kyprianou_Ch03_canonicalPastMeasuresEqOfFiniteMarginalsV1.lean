-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalPastMeasuresEqOfFiniteMarginalsV1
-- name    : Kyprianou.Ch03.canonicalPastMeasuresEqOfFiniteMarginalsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:01:58.456863+00:00
-- url     : https://prove2.me/theorems/65c50f3a-db85-4c31-9c73-b7a9124b1c28
-- title:
--   Finite coordinate marginal equality determines probability on each raw canonical past
-- statement:
--   Finite coordinate cylinders whose time indices are at most t form a pi system generating the raw coordinate sigma algebra. Equality of probability measures on that pi system extends by the measurable-space induction theorem.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; reduction of canonicalDensityProjectiveZeroTransferV1.

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalPastMeasuresEqOfFiniteMarginalsV1
    (Q R : Measure {path : NNReal → ℝ // path 0 = 0}) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (t : NNReal)
    (hMarg : ∀ I : Finset NNReal, (∀ s ∈ I, s ≤ t) →
      Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) R) :
    ∀ A : Set {path : NNReal → ℝ // path 0 = 0}, MeasurableSet[PerfCorrMSQ.natFiltr X t] A → Q A = R A := by
  sorry
