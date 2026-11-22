-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_auxiliary_divisor_gt
-- name    : LongGapsBetweenPrimes.auxiliary_divisor_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:57.245799+00:00
-- url     : https://prove2.me/theorems/70d6687b-892f-417c-a8f3-e8af9d858f47
-- title:
--   Long Gaps Between Primes: auxiliary divisor gt
-- statement:
--   Every nontrivial auxiliary divisor exceeds the lower cutoff `Z`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1573-L1579
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1573-L1579

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.auxiliary_divisor_gt {Z Y d : ℕ} (hd : d ∈ (auxiliaryProduct Z Y).divisors.erase 1) :
    Z < d := by sorry
