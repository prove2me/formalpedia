-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_totient_eq_prod_sub_one_of_squarefree
-- name    : LongGapsBetweenPrimes.totient_eq_prod_sub_one_of_squarefree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:44.278911+00:00
-- url     : https://prove2.me/theorems/2eb29e40-a8fd-4089-a0fa-fce68520127d
-- title:
--   Long Gaps Between Primes: totient eq prod sub one of squarefree
-- statement:
--   For squarefree `d`, its totient is the product of `p - 1` over its prime factors.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L165-L169
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L165-L169

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.totient_eq_prod_sub_one_of_squarefree {d : ℕ} (hd : Squarefree d) :
    d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by sorry
