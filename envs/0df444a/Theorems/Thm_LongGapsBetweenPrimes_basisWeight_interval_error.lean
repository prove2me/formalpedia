-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_basisWeight_interval_error
-- name    : LongGapsBetweenPrimes.basisWeight_interval_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:18.078321+00:00
-- url     : https://prove2.me/theorems/751dff5d-f87d-4820-a19d-01c96564b3c0
-- title:
--   Long Gaps Between Primes: basis Weight interval error
-- statement:
--   A D^6/T error is sufficient after taking κ = 1/8 in the final parameter choice.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2656-L2683
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2656-L2683

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.basisWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1)
    (f : (p : PrimeIndex P) → Option (Fin k) → Fin p.val → ℝ)
    (hfnone : ∀ p t, f p none t = 1) (hf : ∀ p i t, |f p i t| ≤ 1) :
    |integerAverage T (fun n => basisWeight P k D f (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => basisWeight P k D f t ^ 2)| ≤ 16 * D ^ 6 / T := by sorry
