-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
-- name    : Kyprianou.Ch06.twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:20:41.270205+00:00
-- url     : https://prove2.me/theorems/10ec5b17-a6aa-4454-b490-ca302cfecdb3
-- title:
--   Lemma 6.18: two zero-count coordinates and arbitrary compatible outside mark-time rectangles have joint Poisson product law
-- statement:
--   For two disjoint finite-intensity marked-Poisson regions B and D and an arbitrary finite family of pairwise-compatible outside mark-time rectangles, the joint probability of zero initial-to-s and initial-to-t counts in B and D and prescribed outside rectangle increments factors into the two zero Poisson masses and the product of the outside Poisson masses. Outside rectangles may overlap in time when spatially disjoint or overlap spatially when their time intervals are separated.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, joint independence of two competing first-mark regions from the complete outside marked Poisson process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} =
    (ProbabilityTheory.poissonMeasure (s * (n B).toNNReal) {0} *
      ProbabilityTheory.poissonMeasure (t * (n D).toNNReal) {0}) *
    ∏ i : Fin m,
      ProbabilityTheory.poissonMeasure
        ((stops i - starts i) * (n (C i)).toNNReal) {counts i} := by sorry
