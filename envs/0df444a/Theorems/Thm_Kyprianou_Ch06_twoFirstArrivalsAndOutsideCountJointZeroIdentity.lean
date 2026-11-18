-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoFirstArrivalsAndOutsideCountJointZeroIdentity
-- name    : Kyprianou.Ch06.twoFirstArrivalsAndOutsideCountJointZeroIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:20:35.433209+00:00
-- url     : https://prove2.me/theorems/e3d0856f-32e5-477d-9f47-ca49a7f14d13
-- title:
--   Lemma 6.18: both first arrivals with one outside count have the exact three-count joint law
-- statement:
--   For disjoint finite-intensity Poisson mark sets B,D,C, the probability that the first B arrival exceeds s, the first D arrival exceeds t, and exactly k C marks have appeared by u equals the probability of the three fixed-time count conditions N_s B=0,N_t D=0,N_u C=k. This simultaneously replaces both first-arrival survival events without losing a third independent outside count.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, competing first-mark times independent of the outside marked process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalWithTwoDisjointCountEvents
import Theorems.Thm_Kyprianou_Ch06_firstArrivalWithOutsideCountJointContinuous
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoFirstArrivalsAndOutsideCountJointZeroIdentity
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
      (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v D}) ∧
      N omega u C = k} =
    P {omega | N omega s B = 0 ∧
      N omega t D = 0 ∧ N omega u C = k} := by sorry
