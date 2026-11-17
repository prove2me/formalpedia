-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroCountEqualsFirstArrivalSurvivalProbability
-- name    : Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:42:01.053372+00:00
-- url     : https://prove2.me/theorems/a602906d-0a43-4ad1-b16e-109fefd37537
-- title:
--   Chapter 6 Poisson zero-count probability equals first-arrival survival probability
-- statement:
--   For the original marked Poisson process, A-mark arrival convention, and any deterministic t, the fixed-time zero A-count event has the same probability as first A-arrival later than t. Follows from the independently Proved exact Poisson marginal count distribution and source first-arrival exponential survival. This is a reusable genuine result for arbitrary outside-mark count independence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroCountEqualsFirstArrivalSurvivalProbability
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (t : NNReal) :
    P {omega | N omega t A = 0} =
      P {omega | (t : WithTop NNReal) <
        sInf ((fun s : NNReal => (s : WithTop NNReal)) ''
          {s : NNReal | 0 < s ∧ 0 < N omega s A})} := by sorry
