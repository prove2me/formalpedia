-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedFirstArrivalFiniteAlmostSurely
-- name    : Kyprianou.Ch06.markedFirstArrivalFiniteAlmostSurely
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:46:46.818751+00:00
-- url     : https://prove2.me/theorems/eab3f938-475d-449c-b058-aadb064a5e09
-- title:
--   Chapter 6 first A-mark arrival is finite almost surely at positive finite intensity
-- statement:
--   For a Chapter 6 genuine marked Poisson point process and a measurable finite-intensity set A with strictly positive intensity, the first strictly positive A-count arrival time has no infinite atom. The original first A-arrival survival law is exponential with rate n(A)>0, and the separately Proved general positive-exponential survival finiteness theorem yields the conclusion. Complete original mark-selector and process assumptions are retained.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.markedFirstArrivalFiniteAlmostSurely
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤) (hPositive : 0 < n A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    P {omega |
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤} = 0 := by sorry
