-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoCumulativeZeroCountsIndependentOfArbitraryOutsideCountVector
-- name    : Kyprianou.Ch06.twoCumulativeZeroCountsIndependentOfArbitraryOutsideCountVector
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T12:37:29.497197+00:00
-- url     : https://prove2.me/theorems/58aa817f-1245-4c02-8ecd-a7a1e4057ce1
-- title:
--   Lemma 6.18: two competing cumulative zero counts are independent of any finite outside count vector, including overlapping regions
-- statement:
--   For two disjoint finite-intensity mark sets contained in A, the joint event that their cumulative counts at times s and t both vanish is independent of an arbitrary finite vector of cumulative counts outside A, including overlapping outside mark sets and arbitrary observation times. This removes initial-to-time increment notation using the Poisson sample path condition that N(0,S)=0 almost surely.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, finite-dimensional independence of competing mark-arrival observations from the outside marked process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfArbitraryOutsideCountVector
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoCumulativeZeroCountsIndependentOfArbitraryOutsideCountVector
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
      N omega s B = 0 ∧ N omega t D = 0 ∧
      (∀ i : Fin m, N omega (times i) (C i) = counts i)} =
    P {omega |
      N omega s B = 0 ∧ N omega t D = 0} *
    P {omega |
      ∀ i : Fin m, N omega (times i) (C i) = counts i} := by sorry
