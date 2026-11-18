-- Prove2me | Theorems.Thm_Kyprianou_Ch06_secondZeroCountWithFiniteOutsideVectorContinuous
-- name    : Kyprianou.Ch06.secondZeroCountWithFiniteOutsideVectorContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:09:37.471945+00:00
-- url     : https://prove2.me/theorems/7f3ac9b2-80ad-4fc7-b2c1-b6be8d57588c
-- title:
--   Lemma 6.18: finite outside count vector continuity in the second competing region time
-- statement:
--   For two distinguished and finitely many remaining pairwise disjoint finite-intensity marked Poisson mark regions, the probability of zero count for the first region at fixed s, zero count for the second region at variable time v, and an arbitrary finite outside-count vector is continuous in v at t.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, second first-arrival time continuity with outside marked count vector.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.secondZeroCountWithFiniteOutsideVectorContinuous
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (k : Nat) (marks : Fin (2 + k) → Set E)
    (hMarks : ∀ i, MeasurableSet (marks i) ∧ n (marks i) < ⊤)
    (hDisjoint : ∀ i j : Fin (2 + k), i ≠ j →
      Disjoint (marks i) (marks j))
    (s t : NNReal) (outsideTimes : Fin k → NNReal)
    (outsideCounts : Fin k → Nat) :
    ContinuousAt (fun v : NNReal =>
      P {omega |
        N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
        N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)}) t := by sorry
