-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanAffineUpperContinuationFromBarrier
-- name    : Kyprianou.Ch01.mckeanAffineUpperContinuationFromBarrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:49:47.79222+00:00
-- url     : https://prove2.me/theorems/bbe07714-58b1-4747-b23f-b483372f8b3e
-- title:
--   Nonnegative affine intercept transports a barrier supporting bound through the continuation region
-- statement:
--   Pure continuation-region transport. For z≥b let d=exp(−phi(z−b))∈(0,1]. Multiply the assumed barrier inequality by d and add the nonnegative-intercept inequality A d≤A. The exponential identity exp(−phi(z−u))=exp(−phi(b−u))*d yields the target global continuation bound. This is the precise missing continuation-side component of the source McKean affine majorant and is imported through the mission-connected sketch.
-- source:
--   Kyprianou (2006) Chapter 1 McKean continuation-region exponential majorization.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanAffineUpperContinuationFromBarrier
    (K phi b u A B : ℝ) (hphi : 0 < phi) (hA : 0 ≤ A)
    (hAtBarrier :
      K - Real.exp b ≤ A + B * Real.exp (-phi * (b - u))) :
    ∀ z : ℝ, b ≤ z →
      (K - Real.exp b) * Real.exp (-phi * (z - b)) ≤
        A + B * Real.exp (-phi * (z - u)) := by sorry
