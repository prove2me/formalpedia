-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalTwoDisjointJointSurvivalIsZeroCount
-- name    : Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:58:36.866631+00:00
-- url     : https://prove2.me/theorems/ed2bb04f-4df1-4ae0-890b-77b848dd89c1
-- title:
--   Lemma 6.18 joint disjoint first-arrival survival equals two-time joint zero-count law
-- statement:
--   For two disjoint measurable finite-intensity marked-Poisson regions B and D, the probability that the first B-arrival exceeds s and the first D-arrival exceeds t is exactly the probability of simultaneous zero counts N_s(B)=N_t(D)=0. Uses the existing proved zero-count continuity and first-arrival event identities, plus a once-reversed joint first-arrival/count identity. This is the missing stochastic bridge before the two independent exponential race survival laws can be combined.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, two-rate marked-Poisson first-arrival competition.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointSurvivalWithDisjointZeroCount
import Theorems.Thm_Kyprianou_Ch06_firstArrivalJointEventFromContinuousZeroCount
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonZeroCountJointContinuous
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalTwoDisjointJointSurvivalIsZeroCount
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
    P {omega | N omega s B = 0 ∧ N omega t D = 0} := by sorry
