-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_left_bound
-- name    : LongGapsBetweenPrimes.eulerProduct_left_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:27.067833+00:00
-- url     : https://prove2.me/theorems/2d78c625-5a2a-42ce-8cf5-be9e45ac0155
-- title:
--   Long Gaps Between Primes: euler Product left bound
-- statement:
--   Bound the shifted Euler product using the tilt and the largest prime cutoff.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3769-L3811
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3769-L3811

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_left_bound {N : ℕ} {z t : ℝ} (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ z)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z)) := by sorry
