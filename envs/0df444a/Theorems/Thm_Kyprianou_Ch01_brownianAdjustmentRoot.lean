-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
-- name    : Kyprianou.Ch01.brownianAdjustmentRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:06:24.458614+00:00
-- url     : https://prove2.me/theorems/6ffc304d-3e37-4cfb-b741-c2d9cfedb3f0
-- title:
--   Positive Brownian exponential-martingale parameter solves the discounting quadratic
-- statement:
--   For positive Brownian volatility σ and discount q, the positive quadratic root θ=(sqrt(γ²+2σ²q)-γ)/σ² solves σ²θ²/2+γθ=q. This is the exact adjustment-root parameter used to stop the Brownian real exponential martingale in Kyprianou's published solution to Exercise 1.10(ii). No probability assumptions are involved, and the proof follows from positivity and the square-root relation.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), printed solutions pp.306-307, PDF page 158.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianAdjustmentRoot
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    0 < theta ∧ sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q := by sorry
