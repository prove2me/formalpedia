-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sieveT_lower
-- name    : LongGapsBetweenPrimes.sieveT_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:35.646444+00:00
-- url     : https://prove2.me/theorems/a57d9d48-f586-439d-b9a5-06e250ff38f7
-- title:
--   Long Gaps Between Primes: sieve T lower
-- statement:
--   The integer averaging length is at least half of `exp x`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3396-L3398
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3396-L3398

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sieveT_lower {x : ℝ} (hx : 2 ≤ x) : Real.exp x / 2 ≤ (sieveT x : ℝ) := by sorry
