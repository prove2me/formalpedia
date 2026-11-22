-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_long_prime_gaps
-- name    : LongGapsBetweenPrimes.long_prime_gaps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:15:34.3748+00:00
-- url     : https://prove2.me/theorems/8c5c26fd-fab7-475a-974e-a01820141082
-- title:
--   Long Gaps Between Primes: long prime gaps
-- statement:
--   The long-prime-gap statement in the indexed form of `Challenge.lean`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4502-L4539
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4502-L4539

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.long_prime_gaps :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) < X ∧
        c * (Real.log X * Real.log (Real.log X) ^ 2 *
          Real.log (Real.log (Real.log (Real.log X))) /
            Real.log (Real.log (Real.log X)) ^ 2) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by sorry
