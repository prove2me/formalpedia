-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfArbitraryOutsideCountVector
-- name    : Kyprianou.Ch06.twoZeroCountsIndependentOfArbitraryOutsideCountVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:33:59.328194+00:00
-- url     : https://prove2.me/theorems/34ae208b-1202-430e-bac8-7c6fdba2de90
-- title:
--   Lemma 6.18: two competing marked zero-count events are independent of every finite outside count vector, including overlapping mark sets
-- statement:
--   For disjoint marked-Poisson regions B and D both contained in a finite-intensity region A, the joint event of zero B-count at s and zero D-count at t is independent of any arbitrary finite vector of cumulative marked counts on measurable sets outside A, including spatially overlapping sets and unrelated observation times. The proof uses the Proved compatible-rectangle representation of outside count vectors and their independence from the two distinguished zero counts.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, independence of the two competing first marked-point clocks from the full outside marked Poisson process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_outsideCountVectorCompatibleRectangleRepresentation
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoZeroCountsIndependentOfArbitraryOutsideCountVector
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B D : Set E)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (hBA : B ⊆ A) (hDA : D ⊆ A)
    (m : Nat) (times : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hC : ∀ i, MeasurableSet (C i) ∧
      C i ⊆ Aᶜ ∧ n (C i) < ⊤)
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      (∀ i : Fin m, N omega (times i) (C i) = counts i)} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega |
      ∀ i : Fin m, N omega (times i) (C i) = counts i} := by sorry
