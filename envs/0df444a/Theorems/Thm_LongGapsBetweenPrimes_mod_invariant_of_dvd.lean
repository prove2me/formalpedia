-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_mod_invariant_of_dvd
-- name    : LongGapsBetweenPrimes.mod_invariant_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:40.046681+00:00
-- url     : https://prove2.me/theorems/6f6c5064-22b5-40ea-a89b-ae404f93d49f
-- title:
--   Long Gaps Between Primes: mod invariant of dvd
-- statement:
--   Invariance modulo `m` implies invariance modulo every multiple of `m`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2526-L2529
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2526-L2529

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.mod_invariant_of_dvd {m n : ℕ} (hmn : m ∣ n) (f : ℕ → ℝ)
    (hf : ∀ a, f (a % m) = f a) : ∀ a, f (a % n) = f a := by sorry
