-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_eventually_zeroSurvivors_bound
-- name    : LongGapsBetweenPrimes.eventually_zeroSurvivors_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:02.158136+00:00
-- url     : https://prove2.me/theorems/5a57f9a1-f476-4564-9980-e7ef58ec0be2
-- title:
--   Long Gaps Between Primes: eventually zero Survivors bound
-- statement:
--   An explicit `H / log x` bound for the initial sieve's survivors.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4142-L4186
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L4142-L4186

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.eventually_zeroSurvivors_bound : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → (H : ℝ) ≤ x * Real.log x ^ 2 →
      ((zeroSurvivors x H).card : ℝ) ≤ (Real.log 4 + 2) * H / Real.log x := by sorry
