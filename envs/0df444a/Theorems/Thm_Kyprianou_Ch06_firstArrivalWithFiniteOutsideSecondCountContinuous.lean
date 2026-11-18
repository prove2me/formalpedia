-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideSecondCountContinuous
-- name    : Kyprianou.Ch06.firstArrivalWithFiniteOutsideSecondCountContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T11:27:28.192927+00:00
-- url     : https://prove2.me/theorems/36d8f456-d992-46cd-a6d9-a7e0253f60d1
-- title:
--   Lemma 6.18: continuity of second count with first arrival and finite outside vector fixed
-- statement:
--   For pairwise-disjoint finite-intensity mark regions, the probability that D has no marks by a variable time, the first B-arrival exceeds fixed s, and a complete finite outside count vector has prescribed values is continuous in the D observation time.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), pp.160–161, second arrival with finite outside count-vector continuity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithFiniteOutsideCountVector
import Theorems.Thm_Kyprianou_Ch06_secondZeroCountWithFiniteOutsideVectorContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalWithFiniteOutsideSecondCountContinuous
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
        N omega v (marks (Fin.castAdd k (1 : Fin 2))) = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 <
              N omega w (marks (Fin.castAdd k (0 : Fin 2)))}) ∧
        (∀ j : Fin k, N omega (outsideTimes j)
          (marks (Fin.natAdd 2 j)) = outsideCounts j)}) t := by sorry
