-- Prove2me | Theorems.Thm_Kyprianou_Ch06_beforeFirstArrivalImpliesZeroCount
-- name    : Kyprianou.Ch06.beforeFirstArrivalImpliesZeroCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:43:26.624169+00:00
-- url     : https://prove2.me/theorems/0515a35f-b4d6-487e-af6f-ed87e78011c5
-- title:
--   Lemma 6.18: count is zero strictly before first positive marked arrival
-- statement:
--   For an integer-valued marked count N initially zero at time zero, any observation time t strictly preceding the infimum of positive-count, positive-time arrivals must have zero count N_t. The statement is deterministic and requires no monotonicity or stochastic independence; it handles t=0 explicitly.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, first marked Poisson event and competing-arrival sample paths.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.beforeFirstArrivalImpliesZeroCount
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (A : Set E)
    (hInit : N omega 0 A = 0) (t : NNReal)
    (hBefore : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})) :
    N omega t A = 0 := by sorry
