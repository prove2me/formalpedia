-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eventually_sieveY_lt_primorial
-- name    : LongGapsBetweenPrimes.eventually_sieveY_lt_primorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:05.628798+00:00
-- url     : https://prove2.me/theorems/c4b161b5-558c-4069-8e78-7617143b3aca
-- title:
--   Long Gaps Between Primes: eventually sieve Y lt primorial
-- statement:
--   The upper sieve cutoff is eventually below the primorial up to `x`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3544-L3581
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3544-L3581

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eventually_sieveY_lt_primorial : ∀ᶠ x : ℝ in Filter.atTop,
    sieveY x < primorial ⌊x⌋₊ := by sorry
