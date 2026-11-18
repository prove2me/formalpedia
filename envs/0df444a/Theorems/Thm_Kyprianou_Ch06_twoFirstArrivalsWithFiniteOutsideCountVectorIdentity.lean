-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
-- name    : Kyprianou.Ch06.twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:31:27.493896+00:00
-- url     : https://prove2.me/theorems/e7d85da1-1199-4733-ad0e-40bbc7ba18a7
-- title:
--   Lemma 6.18: two competing first-arrival survivals with arbitrary finite outside counts equal corresponding zero-count event
-- statement:
--   For two distinguished and finitely many remaining pairwise disjoint finite-intensity Poisson mark regions, the probability of both competing first-arrival times exceeding prescribed times and a finite outside-count vector taking prescribed values equals the corresponding three-part count-cylinder probability.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, simultaneous first-arrival survival and independence from outside mark observations.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideCountVector
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideSecondCountContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
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
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (1 : Fin 2)))}) ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by sorry
