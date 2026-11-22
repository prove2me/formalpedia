-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficient_noncoprime_le
-- name    : LongGapsBetweenPrimes.coefficient_noncoprime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:51.120374+00:00
-- url     : https://prove2.me/theorems/ed8092f2-0506-4301-ade5-cf01245c1814
-- title:
--   Long Gaps Between Primes: coefficient noncoprime le
-- statement:
--   Bound the coefficient mass of divisors sharing a prime with `m` by a prime sum.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2843-L2875
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2843-L2875

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficient_noncoprime_le {P m : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hm : m ∣ P) (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient) ≤
      ∑ p ∈ m.primeFactors, 4 / (p : ℝ) := by sorry
