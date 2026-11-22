-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_mem_auxiliaryPrimes
-- name    : LongGapsBetweenPrimes.mem_auxiliaryPrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:45.385311+00:00
-- url     : https://prove2.me/theorems/e48b7765-242a-4a7a-9d34-25e9cf6ba7b0
-- title:
--   Long Gaps Between Primes: mem auxiliary Primes
-- statement:
--   Membership in the auxiliary primes means primality and `Z < p ≤ Y`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1193-L1196
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1193-L1196

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.mem_auxiliaryPrimes {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by sorry
