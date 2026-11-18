-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalJointSurvivalWithDisjointZeroCount
-- name    : Kyprianou.Ch06.firstArrivalJointSurvivalWithDisjointZeroCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:55:42.695371+00:00
-- url     : https://prove2.me/theorems/8a47f1ea-823f-4317-b878-334b6893937c
-- title:
--   Lemma 6.18: joint first-arrival survival and disjoint Poisson zero count identity
-- statement:
--   For two disjoint finite-intensity measurable Poisson mark regions B and D, the joint probability that first B-arrival occurs strictly after s and N_t(D)=0 equals the joint zero-count probability N_s(B)=N_t(D)=0. The identity is valid at arbitrary nonnegative s,t and uses the pinned already Proved joint zero-count continuity and general first-arrival/zero-count event identity. It is the first needed stochastic step in the two-rate first-mark race argument.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first-arrival competition for disjoint regions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalJointSurvivalWithDisjointZeroCount
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
      N omega t D = 0} =
    P {omega | N omega s B = 0 ∧ N omega t D = 0} := by sorry
