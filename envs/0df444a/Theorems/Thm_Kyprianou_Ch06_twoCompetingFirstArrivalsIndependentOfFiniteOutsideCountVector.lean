-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoCompetingFirstArrivalsIndependentOfFiniteOutsideCountVector
-- name    : Kyprianou.Ch06.twoCompetingFirstArrivalsIndependentOfFiniteOutsideCountVector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:18:59.566207+00:00
-- url     : https://prove2.me/theorems/680cfd9a-672a-48b1-8d92-f8345c9e7b51
-- title:
--   Lemma 6.18: two competing first arrivals are independent of every finite disjoint outside count cylinder
-- statement:
--   For two distinguished and finitely many remaining pairwise-disjoint finite-intensity Poisson mark sets, the joint survival event of the two first-arrival times is independent of an arbitrary finite outside count-vector cylinder, with no restriction that the times be equal or ordered.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, first marked Poisson point independence from the outside-A marked point process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsWithFiniteOutsideCountVectorIdentity
import Theorems.Thm_Kyprianou_Ch06_disjointTwoZeroCountsIndependentOfFiniteOutsideVector
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoCompetingFirstArrivalsIndependentOfFiniteOutsideCountVector
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
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 <
            N omega v (marks (Fin.castAdd k (1 : Fin 2)))})} *
    P {omega | (∀ j : Fin k, N omega (outsideTimes j)
        (marks (Fin.natAdd 2 j)) = outsideCounts j)} := by sorry
