-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_antitone
-- name    : LongGapsBetweenPrimes.eulerProduct_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:44.84808+00:00
-- url     : https://prove2.me/theorems/5d38ebfc-fc69-4824-8955-cec9778133b6
-- title:
--   Long Gaps Between Primes: euler Product antitone
-- statement:
--   The finite Euler product decreases as its positive exponent increases.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1167-L1180
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1167-L1180

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eulerProduct_antitone (N : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) :
    eulerProduct N τ ≤ eulerProduct N σ := by sorry
