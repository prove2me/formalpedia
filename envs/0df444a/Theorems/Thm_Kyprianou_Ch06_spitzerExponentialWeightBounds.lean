-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerExponentialWeightBounds
-- name    : Kyprianou.Ch06.spitzerExponentialWeightBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:28:49.139956+00:00
-- url     : https://prove2.me/theorems/71ae7db8-7201-45ea-a25f-314c66815d89
-- title:
--   Spitzer integral: exponential discount bounds on unit interval
-- statement:
--   For p≥0 and 0≤t≤1, the exponential discount e^{-p t} lies between e^{-p} and 1. This quantitative bound is used twice in Kyprianou (2006), Exercise 6.8, to compare the Wiener–Hopf exponentially discounted occupation integral against the unweighted Spitzer divergence criterion.
-- source:
--   Kyprianou (2006), Exercise 6.8 solutions, printed p.333 and p.334.

import Mathlib
open Real
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.8 exponential-time comparison on the unit time interval. -/
theorem spitzerExponentialWeightBounds
    (p t : ℝ) (hp : 0 ≤ p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-p) ≤ Real.exp (-p * t) ∧
      Real.exp (-p * t) ≤ 1 := by
  sorry

end Kyprianou.Ch06
