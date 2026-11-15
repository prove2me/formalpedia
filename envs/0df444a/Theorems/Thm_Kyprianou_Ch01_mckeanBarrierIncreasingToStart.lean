-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBarrierIncreasingToStart
-- name    : Kyprianou.Ch01.mckeanBarrierIncreasingToStart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:59:32.001198+00:00
-- url     : https://prove2.me/theorems/b0394597-3452-4cea-833a-f9928f2b871b
-- title:
--   McKean perpetual put barrier: payoff monotonicity below the barrier
-- statement:
--   For a <= x <= b, the positive-strike perpetual put barrier payoff at a is at most the immediate-exercise payoff K-exp(x), where b=log(K phi/(1+phi)).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(iii), printed p. 31; original parent bea9bdc1-0ec7-448d-8142-15743baf5c77.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBarrierIncreasingToStart
    (K phi x b a : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hb : b = Real.log (K * phi / (1 + phi)))
    (ha : a ≤ x) (hx : x ≤ b) :
    (K - Real.exp a) * Real.exp (-phi * (x - a)) ≤
      K - Real.exp x := by sorry
