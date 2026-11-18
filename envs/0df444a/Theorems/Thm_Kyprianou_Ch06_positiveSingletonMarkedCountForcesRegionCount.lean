-- Prove2me | Theorems.Thm_Kyprianou_Ch06_positiveSingletonMarkedCountForcesRegionCount
-- name    : Kyprianou.Ch06.positiveSingletonMarkedCountForcesRegionCount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:43:45.598203+00:00
-- url     : https://prove2.me/theorems/da10a4d3-9b2c-4285-b861-e3f1eee43fb4
-- title:
--   Lemma 6.18: a positive singleton mark count forces positive count in every containing region
-- statement:
--   For any finitely additive nonnegative integer marked-count function and any x in a mark set D, a positive count at the singleton {x} implies a positive count over D at the same observation time. This is the pathwise inference needed to identify the winning mark in a two-region Poisson first-arrival race.
-- source:
--   Kyprianou (2006), Lemma 6.18, printed pp.160–161, first-mark identity and pathwise additivity.

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.positiveSingletonMarkedCountForcesRegionCount
    {Omega E : Type}
    (N : Omega → NNReal → Set E → Nat)
    (omega : Omega) (t : NNReal)
    (x : E) (D : Set E) (hx : x ∈ D)
    (hAdd : ∀ A B : Set E, Disjoint A B →
      N omega t (A ∪ B) = N omega t A + N omega t B)
    (hPositive : 0 < N omega t ({x} : Set E)) :
    0 < N omega t D := by sorry
