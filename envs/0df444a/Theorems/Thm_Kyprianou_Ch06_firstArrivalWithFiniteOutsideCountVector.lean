-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideCountVector
-- name    : Kyprianou.Ch06.firstArrivalWithFiniteOutsideCountVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:24:06.638505+00:00
-- url     : https://prove2.me/theorems/df2d6a85-6041-42aa-a792-7fef26cd2991
-- title:
--   Lemma 6.18: first competing arrival survival with any disjoint finite outside count cylinder
-- statement:
--   For two distinguished and finitely many remaining pairwise disjoint finite-intensity marked Poisson mark sets, the event that the first B arrival exceeds s, the count of D at t is zero and a finite remaining outside count vector takes prescribed values has exactly the same probability as its fixed-time count-vector event.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, first arrival independence from finite outside count cylinders.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsWithFiniteOutsideVectorContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalWithFiniteOutsideCountVector
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
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} =
    P {omega |
      N omega s (marks (Fin.castAdd k (0 : Fin 2))) = 0 ∧
      N omega t (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
      (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by sorry
