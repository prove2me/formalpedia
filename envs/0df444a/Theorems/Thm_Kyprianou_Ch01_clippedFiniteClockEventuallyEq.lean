-- Prove2me | Theorems.Thm_Kyprianou_Ch01_clippedFiniteClockEventuallyEq
-- name    : Kyprianou.Ch01.clippedFiniteClockEventuallyEq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:56:46.799006+00:00
-- url     : https://prove2.me/theorems/afaf3c70-2e2f-4ecf-b71a-a97860aae405
-- title:
--   A finite stopping time is eventually unchanged by integer-horizon clipping
-- statement:
--   For each finite nonnegative real time t there is an integer N beyond t. Every n≥N then satisfies t≤n, so min(t,n)=t and untopD n of its WithTop lift equals t. This is the finite stopping-time branch of pathwise convergence of the true clipped McKean payoff.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13; finite stopping time clipped horizon.

import Mathlib
open Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.clippedFiniteClockEventuallyEq
    (t : ℝ≥0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (min (t : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD
        (n : ℝ≥0) = t := by sorry
