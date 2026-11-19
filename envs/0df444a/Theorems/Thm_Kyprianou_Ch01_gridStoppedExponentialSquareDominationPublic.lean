-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gridStoppedExponentialSquareDominationPublic
-- name    : Kyprianou.Ch01.gridStoppedExponentialSquareDominationPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:01:29.35655+00:00
-- url     : https://prove2.me/theorems/7ca50141-6d47-4828-a6a4-44535995ca80
-- title:
--   Public squared stopped Brownian exponential domination by doubled-parameter exponential
-- statement:
--   For any capped integer stopping index and positive horizon, the square of the Gaussian exponential compensated by its adjustment-root rate is pointwise bounded by the doubled-parameter compensated exponential multiplied by exp(sigma²theta² times the maximum physical time). This deterministic identity uses only the root equality and capped stopping index.
-- source:
--   Authoritatively accepted Kyprianou.Ch01.gridStoppedExponentialSquareDomination, an algebraic auxiliary for Exercise 1.10(ii).

import Mathlib.Analysis.Complex.Exponential
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gridStoppedExponentialSquareDominationPublic {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta q : ℝ)
    (hroot : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q)
    (delta : ℝ≥0) (tau : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, tau ω ≤ N) (ω : Ω) :
    Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
      q * (((tau ω : ℝ≥0) * delta) : ℝ)) ^ 2 ≤
    Real.exp (sigma ^ 2 * theta ^ 2 * (((N : ℝ≥0) * delta) : ℝ)) *
      Real.exp ((2 * theta) * X ((tau ω : ℝ≥0) * delta) ω -
        (sigma ^ 2 * (2 * theta) ^ 2 / 2 + gamma * (2 * theta)) *
          (((tau ω : ℝ≥0) * delta) : ℝ)) := by sorry
