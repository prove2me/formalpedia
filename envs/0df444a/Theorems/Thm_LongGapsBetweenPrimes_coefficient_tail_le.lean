-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficient_tail_le
-- name    : LongGapsBetweenPrimes.coefficient_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:53.688994+00:00
-- url     : https://prove2.me/theorems/b54bb588-e71d-48cf-a308-d1b10de23d37
-- title:
--   Long Gaps Between Primes: coefficient tail le
-- statement:
--   Rankin's bound for the absolute coefficient tail.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2914-L2926
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2914-L2926

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficient_tail_le {P : ℕ} {v β : ℝ} (hv : 1 ≤ v) (hβ : 0 ≤ β) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => v < (d : ℝ)), |coefficient P d| / d.totient) ≤
      v ^ (-β) * coefficientAbsMoment P β := by sorry
