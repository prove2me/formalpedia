-- Prove2me | Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonRectangles
-- name    : Kyprianou.Ch06.threeDisjointMarkedPoissonRectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:14:04.881205+00:00
-- url     : https://prove2.me/theorems/7326d948-63bc-4888-8060-715a9d133eac
-- title:
--   Chapter 6: independent joint count law for three spatially disjoint Poisson rectangles
-- statement:
--   Under the original Chapter 6 marked Poisson point process hypotheses, the three count increments from zero to arbitrary deterministic times for three pairwise disjoint measurable finite-intensity mark sets have the joint law of three independent Poisson random variables. This is an exact three-rectangle specialisation of the source process axiom, a finite-dimensional step towards the first-mark independence in Lemma 6.18.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.threeDisjointMarkedPoissonRectangles
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFiniteA : n A < ⊤) (hFiniteB : n B < ⊤)
    (hFiniteC : n C < ⊤)
    (s t u : NNReal) (k l r : Nat) :
    P {omega | N omega s A - N omega 0 A = k ∧
      N omega t B - N omega 0 B = l ∧
      N omega u C - N omega 0 C = r} =
    ProbabilityTheory.poissonMeasure
      (s * (n A).toNNReal) {k} *
    ProbabilityTheory.poissonMeasure
      (t * (n B).toNNReal) {l} *
    ProbabilityTheory.poissonMeasure
      (u * (n C).toNNReal) {r} := by sorry
