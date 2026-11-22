-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_finite_simultaneous_roots
-- name    : LongGapsBetweenPrimes.finite_simultaneous_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:53.588371+00:00
-- url     : https://prove2.me/theorems/8881dc9c-b590-493e-bbea-8fcd7de412b5
-- title:
--   Long Gaps Between Primes: finite simultaneous roots
-- statement:
--   The finite weighted sieve, with every numerical loss displayed explicitly.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3254-L3296
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3254-L3296

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.finite_simultaneous_roots {P M k T : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (hM : 1 < M) (hT : 0 < T) (hmin : ∀ p ∈ P.primeFactors, M < p)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (htail : D ^ (-β) * Real.exp (((k + 1 : ℕ) : ℝ) * C * β) +
      16 * (((k + 1 : ℕ) : ℝ)) ^ 2 / M ≤ 1 / 2)
    (hgram : gramBound (k + 1) M D ≤ 5 / 4)
    (herr : 16 * D ^ 6 / T ≤ 1 / 8)
    (hbad : (((k + 1 : ℕ) : ℝ)) * (uncoveredBound k β C M D + 16 * D ^ 6 / T) < 1 / 4) :
    ∃ n < T, ∀ i : Fin (k + 1), ∃ p : PrimeIndex P, residueVector P n p = root p i := by sorry
