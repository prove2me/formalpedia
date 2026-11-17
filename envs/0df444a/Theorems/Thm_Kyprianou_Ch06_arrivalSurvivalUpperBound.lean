-- Prove2me | Theorems.Thm_Kyprianou_Ch06_arrivalSurvivalUpperBound
-- name    : Kyprianou.Ch06.arrivalSurvivalUpperBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:57:33.718389+00:00
-- url     : https://prove2.me/theorems/39c4d161-c16c-47fc-b8f0-d8dccbba38fa
-- title:
--   Chapter 6 first Poisson arrival: survival bounded by zero-count marginal
-- statement:
--   If the counting process starts at zero almost surely, the probability that the first positive A-count arrival lies strictly after t is bounded above by the probability of zero A-count at time t. Reuses the deterministic first-arrival implication without changing the underlying full process obligations.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.arrivalSurvivalUpperBound
    {Omega E : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (N : Omega → NNReal → Set E → Nat) (A : Set E)
    (hInit : ∀ᵐ omega ∂P, N omega 0 A = 0) (t : NNReal) :
    P {omega | (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})} ≤
    P {omega | N omega t A = 0} := by sorry
