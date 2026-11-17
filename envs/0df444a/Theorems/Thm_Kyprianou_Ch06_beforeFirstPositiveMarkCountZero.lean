-- Prove2me | Theorems.Thm_Kyprianou_Ch06_beforeFirstPositiveMarkCountZero
-- name    : Kyprianou.Ch06.beforeFirstPositiveMarkCountZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:54:27.433924+00:00
-- url     : https://prove2.me/theorems/df2bc6b9-6676-4190-8350-69e3fb3186d2
-- title:
--   Chapter 6 first Poisson arrival: no previous positive count
-- statement:
--   A sample path with N(0,A)=0 and first strictly-positive A-count time sigma must have N(t,A)=0 whenever t is strictly earlier than sigma. This deterministic order-theoretic lemma preserves the complete first-arrival convention, including the empty arrival set and t=0.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.beforeFirstPositiveMarkCountZero
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (omega : Omega)
    (hzero : N omega 0 A = 0)
    (t : NNReal)
    (hBefore : (t : WithTop NNReal) <
      sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
        {u : NNReal | 0 < u ∧ 0 < N omega u A})) :
    N omega t A = 0 := by sorry
