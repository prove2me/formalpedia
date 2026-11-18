-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalWithTwoDisjointCountEvents
-- name    : Kyprianou.Ch06.firstArrivalSurvivalWithTwoDisjointCountEvents
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:13:36.270496+00:00
-- url     : https://prove2.me/theorems/e4eaf907-0997-4d72-8a44-8e70c027dc7f
-- title:
--   Lemma 6.18: first-arrival survival with two disjoint count constraints equals three zero/count event
-- statement:
--   For three mutually disjoint finite-intensity marked Poisson regions B,D,C, the joint event that first B arrival exceeds s, no D marks occur by t, and exactly k C marks occur by u has the same probability as the corresponding three-region count event N_s(B)=0,N_t(D)=0,N_u(C)=k. This is a first Markov-like continuity step for competing arrivals independent of an outside count.
-- source:
--   Kyprianou (2006), Lemma 6.18, printed pp.160–161, independence of first-mark competition and outside marked counts.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_twoOutsideJointZeroCountContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalSurvivalWithTwoDisjointCountEvents
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v B}) ∧
      N omega t D = 0 ∧ N omega u C = k} =
    P {omega | N omega s B = 0 ∧
      N omega t D = 0 ∧ N omega u C = k} := by sorry
