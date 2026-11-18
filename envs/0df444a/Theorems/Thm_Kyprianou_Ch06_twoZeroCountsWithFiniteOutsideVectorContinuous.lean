-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoZeroCountsWithFiniteOutsideVectorContinuous
-- name    : Kyprianou.Ch06.twoZeroCountsWithFiniteOutsideVectorContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:09:29.587062+00:00
-- url     : https://prove2.me/theorems/c4208aba-d46b-43b4-a187-403a78bbe674
-- title:
--   Lemma 6.18: continuity of competing zero-count events with a finite outside vector
-- statement:
--   For pairwise disjoint finite-intensity mark sets, the probability of zero counts in two distinguished regions, with the first observation time varying and all counts in a remaining finite outside vector fixed, is continuous in the first time. Factorisation by count-vector independence and established two-region zero-count continuity yields the claim.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, first arrival and finite outside Poisson count-vector continuity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoZeroCountsWithFiniteOutsideVectorContinuous
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
    ContinuousAt (fun v : NNReal =>
      P {omega |
      N omega v (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)}) s := by sorry
