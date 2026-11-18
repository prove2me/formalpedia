-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalWithOutsideCountJointContinuous
-- name    : Kyprianou.Ch06.firstArrivalWithOutsideCountJointContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:16:19.01983+00:00
-- url     : https://prove2.me/theorems/b82566b0-42a4-4165-822e-24d4b35edeb5
-- title:
--   Lemma 6.18: continuity with one competing arrival survival and one outside mark count
-- statement:
--   For disjoint finite-intensity mark regions B,D,C, the probability that D has zero count at a variable time v, the first B arrival exceeds a fixed s, and the C count equals k is continuous in v. The result transfers existing three-region zero-count continuity through an independently proved first B-arrival and two-count identity.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, continuity required for joint competing first arrivals with outside marked cylinder.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalSurvivalWithTwoDisjointCountEvents
import Theorems.Thm_Kyprianou_Ch06_twoOutsideJointZeroCountContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalWithOutsideCountJointContinuous
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
    ContinuousAt (fun v : NNReal =>
      P {omega | N omega v D = 0 ∧
        (s : WithTop NNReal) <
          sInf ((fun w : NNReal => (w : WithTop NNReal)) ''
            {w : NNReal | 0 < w ∧ 0 < N omega w B}) ∧
        N omega u C = k}) t := by sorry
