-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoDisjointMarkedPoissonRectangles
-- name    : Kyprianou.Ch06.twoDisjointMarkedPoissonRectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:06:49.524593+00:00
-- url     : https://prove2.me/theorems/e51e23a2-100f-45dc-8c46-e03df11ab530
-- title:
--   Chapter 6 marked Poisson disjoint spatial rectangles have independent joint count law
-- statement:
--   For any two measurable finite-intensity disjoint mark sets A and B and deterministic times s and t, the initial-to-s A-count increment and initial-to-t B-count increment have the joint law of independent Poisson variables. It is the spatially disjoint two-rectangle specialisation of the full marked Poisson process hypothesis and a useful source-faithful step towards Lemma 6.18 outside-mark independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoDisjointMarkedPoissonRectangles
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (s t : NNReal) (k l : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t B - N omega 0 B = l} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      (t * (n B).toNNReal) {l} := by sorry
