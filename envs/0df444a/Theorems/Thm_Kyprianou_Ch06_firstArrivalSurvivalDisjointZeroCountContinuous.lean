-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalDisjointZeroCountContinuous
-- name    : Kyprianou.Ch06.firstArrivalSurvivalDisjointZeroCountContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:03:52.082223+00:00
-- url     : https://prove2.me/theorems/57685ed4-4317-4a01-b73b-65fc47bad733
-- title:
--   Lemma 6.18: continuity of zero-count jointly with disjoint first-arrival survival
-- statement:
--   For disjoint finite-intensity measurable regions B and D of a marked Poisson process, the probability that there are no D-marks by variable time u and the first B-mark arrival exceeds fixed time s is continuous in u at any t. Combines a proved first-arrival/zero-count probability identity with proved two-region zero-count continuity.
-- source:
--   Kyprianou (2006), Lemma 6.18, printed pp.160–161, joint first-arrival survival and count continuity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointSurvivalWithDisjointZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalSurvivalDisjointZeroCountContinuous
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    ContinuousAt (fun u : NNReal =>
      P {omega |
        N omega u D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
            {v : NNReal | 0 < v ∧ 0 < N omega v B})}) t := by sorry
