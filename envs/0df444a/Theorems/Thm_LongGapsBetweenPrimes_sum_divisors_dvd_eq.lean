-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_sum_divisors_dvd_eq
-- name    : LongGapsBetweenPrimes.sum_divisors_dvd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:21.423802+00:00
-- url     : https://prove2.me/theorems/125661bf-af30-462b-85b8-4439a10493de
-- title:
--   Long Gaps Between Primes: sum divisors dvd eq
-- statement:
--   Divisors divisible by p are parametrized by the divisors of P/p.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L811-L830
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L811-L830

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.sum_divisors_dvd_eq {P p : ℕ} (hP : P ≠ 0) (hp : 0 < p) (hpP : p ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), f d) =
      ∑ e ∈ (P / p).divisors, f (p * e) := by sorry
