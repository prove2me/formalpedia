-- Prove2me | Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
-- name    : Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:38:24.63793+00:00
-- url     : https://prove2.me/theorems/cdc47666-4ec9-44d8-a600-1ba9494f11d8
-- title:
--   Lemma 6.18: competing zero-count event independent of arbitrary finite disjoint outside count vector
-- statement:
--   For a finite family of pairwise-disjoint measurable finite-intensity mark sets, two selected sets B,D and any number of remaining outside regions, the event of zero B and D counts at arbitrary s,t is independent of the complete outside count vector at arbitrary observation times.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, independence from the complete outside marked-Poisson count vector.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedCountVectorTwoPlusRestIndependent
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfFiniteOutsideVector
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (marks : Fin (2 + k) → Set E)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j))
    (s t : NNReal) (outsideTimes : Fin k → NNReal)
    (outsideCounts : Fin k → Nat) :
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0} *
    P {omega | ∀ j : Fin k, N omega (outsideTimes j)
      (marks (Fin.natAdd 2 j)) = outsideCounts j} := by sorry
