-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_normalizer_lower_bound
-- name    : LongGapsBetweenPrimes.normalizer_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:36.634678+00:00
-- url     : https://prove2.me/theorems/b226b585-648e-4afa-8b7c-3efb749300be
-- title:
--   Long Gaps Between Primes: normalizer lower bound
-- statement:
--   A logarithmic lower bound for the auxiliary normalizer.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1387-L1400
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1387-L1400

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.normalizer_lower_bound {Z Y : ℕ} (hZY : Z ≤ Y) {A : ℝ}
    (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hAY : A ≤ Real.log ((Y : ℝ) + 1)) :
    Real.log (Real.log ((Y : ℝ) + 1)) - Real.log A - 2 ≤
      2 * A * normalizer (auxiliaryProduct Z Y) := by sorry
