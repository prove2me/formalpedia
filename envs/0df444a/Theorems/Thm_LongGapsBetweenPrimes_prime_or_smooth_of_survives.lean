-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_prime_or_smooth_of_survives
-- name    : LongGapsBetweenPrimes.prime_or_smooth_of_survives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:42.176668+00:00
-- url     : https://prove2.me/theorems/00db6e17-872a-4e3f-934b-1cb28d13b559
-- title:
--   Long Gaps Between Primes: prime or smooth of survives
-- statement:
--   The initial zero-residue sieve leaves only primes and z-smooth integers.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L374-L402
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L374-L402

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.prime_or_smooth_of_survives {n H : ℕ} {x w z : ℝ}
    (hn : 1 ≤ n) (hnH : n ≤ H) (hx : 0 < x) (hsmall : 2 * (H : ℝ) < x * w)
    (hsurvives : ∀ p : ℕ, p.Prime → ((p : ℝ) ≤ w ∨ (z < p ∧ (p : ℝ) ≤ x / 2)) → ¬p ∣ n) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ z := by sorry
