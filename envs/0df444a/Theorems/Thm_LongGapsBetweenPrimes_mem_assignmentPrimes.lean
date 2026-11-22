-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_mem_assignmentPrimes
-- name    : LongGapsBetweenPrimes.mem_assignmentPrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:52.18377+00:00
-- url     : https://prove2.me/theorems/0335dcd1-1924-4b79-a097-d296e9e3b675
-- title:
--   Long Gaps Between Primes: mem assignment Primes
-- statement:
--   A prime belongs to the assigned set exactly when its assignment is nonempty.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2389-L2392
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2389-L2392

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.mem_assignmentPrimes {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) :
    p.val ∈ assignmentPrimes σ ↔ (σ p).isSome := by sorry
