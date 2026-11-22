-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_zeroCoverPrimes_subset
-- name    : LongGapsBetweenPrimes.zeroCoverPrimes_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:27.002918+00:00
-- url     : https://prove2.me/theorems/3e128005-17fb-481a-a3a5-80bda3d15c66
-- title:
--   Long Gaps Between Primes: zero Cover Primes subset
-- statement:
--   Every prime in the zero-residue sieve is at most `x`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4270-L4276
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4270-L4276

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.zeroCoverPrimes_subset {x : ℝ} (hx : 0 ≤ x) (hW : coverW x ≤ ⌊x⌋₊) :
    zeroCoverPrimes x ⊆ ⌊x⌋₊.primesLE := by sorry
