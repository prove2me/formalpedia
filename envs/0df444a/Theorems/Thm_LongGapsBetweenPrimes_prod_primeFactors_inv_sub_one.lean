-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prod_primeFactors_inv_sub_one
-- name    : LongGapsBetweenPrimes.prod_primeFactors_inv_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:50.932567+00:00
-- url     : https://prove2.me/theorems/99585cc1-8c82-49c8-b18a-fca7fe8fcf69
-- title:
--   Long Gaps Between Primes: prod prime Factors inv sub one
-- statement:
--   For squarefree `d`, the product of `1 / (p - 1)` equals `1 / φ(d)`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2198-L2205
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2198-L2205

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prod_primeFactors_inv_sub_one {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by sorry
