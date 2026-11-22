-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_normalizer_lower_integral
-- name    : LongGapsBetweenPrimes.normalizer_lower_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:31.550953+00:00
-- url     : https://prove2.me/theorems/37ab26db-d5cb-49b0-ba42-b3979fc8b1b0
-- title:
--   Long Gaps Between Primes: normalizer lower integral
-- statement:
--   Integrating the lower Euler-product bound gives a completely finite
--   lower bound for B; no sieve asymptotic is assumed.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1354-L1384
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1354-L1384

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.normalizer_lower_integral {Z Y : ℕ} (hZY : Z ≤ Y) {A a b : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ a * Real.log ((Y : ℝ) + 1)) :
    (Real.log b - Real.log a) / (2 * A) - (b - a) ≤ normalizer (auxiliaryProduct Z Y) := by sorry
