-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoDisjointMarkedFirstArrivalsJointExponentialSurvival
-- name    : Kyprianou.Ch06.twoDisjointMarkedFirstArrivalsJointExponentialSurvival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:09:09.896726+00:00
-- url     : https://prove2.me/theorems/9e8a21ad-64b8-4762-851f-98d5362fdddf
-- title:
--   Lemma 6.18: joint first-arrival survival of two disjoint Poisson mark regions factorises exponentially
-- statement:
--   The joint survival probability for the first arrival times into two measurable disjoint finite-intensity mark regions B,D equals the product of their exponential survival probabilities at arbitrary s,t. This supplies the two-variable independent exponential-race survival law used to prove the first-mark distribution.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, competing Poisson first mark distribution.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedZeroCountsJointExponential
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoDisjointMarkedFirstArrivalsJointExponentialSurvival
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (s t : NNReal) :
    P {omega |
      (s : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u B}) ∧
      (t : WithTop NNReal) <
        sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ 0 < N omega u D})} =
    ENNReal.ofReal
      (Real.exp (-(((n B).toNNReal : Real) * (s : Real)))) *
    ENNReal.ofReal
      (Real.exp (-(((n D).toNNReal : Real) * (t : Real)))) := by sorry
