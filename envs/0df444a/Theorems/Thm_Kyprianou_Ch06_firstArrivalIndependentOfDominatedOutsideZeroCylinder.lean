-- Prove2me | Theorems.Thm_Kyprianou_Ch06_firstArrivalIndependentOfDominatedOutsideZeroCylinder
-- name    : Kyprianou.Ch06.firstArrivalIndependentOfDominatedOutsideZeroCylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:04:09.911764+00:00
-- url     : https://prove2.me/theorems/a100f010-2e4b-4de3-b3de-8eea9e538de0
-- title:
--   First A-arrival independent of an arbitrary finite dominated outside-A zero-count cylinder
-- statement:
--   For the genuine original Chapter 6 marked Poisson and first A-mark model, any finite-dimensional outside-A count cylinder whose counts all equal zero and which contains an observation u dominating all other mark sets and observation times is independent of first A-arrival survival. The a.e source mark/time monotonicity reduces the entire cylinder to the single dominant zero-count event, and the previously Proved singleton outside-A count independence gives the exact factorisation. Retains arbitrary m, mark family, times and positive/zero A intensity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.firstArrivalIndependentOfDominatedOutsideZeroCylinder
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A) (hFA : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x}))
    (m : Nat) (times : Fin m → NNReal) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i) ∧ B i ⊆ Aᶜ ∧ n (B i) < ⊤)
    (u : Fin m) (hDom : ∀ i : Fin m,
      B i ⊆ B u ∧ times i ≤ times u) (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A}) ∧
      (∀ i : Fin m, N omega (times i) (B i) = 0)} =
    P {omega | (t : WithTop NNReal) <
        sInf ((fun v : NNReal => (v : WithTop NNReal)) ''
          {v : NNReal | 0 < v ∧ 0 < N omega v A})} *
    P {omega | ∀ i : Fin m, N omega (times i) (B i) = 0} := by sorry
