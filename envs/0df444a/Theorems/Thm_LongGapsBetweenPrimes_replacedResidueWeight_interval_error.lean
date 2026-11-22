-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_interval_error
-- name    : LongGapsBetweenPrimes.replacedResidueWeight_interval_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:43.459895+00:00
-- url     : https://prove2.me/theorems/b64f84a6-3eac-4bcd-ba2e-104d38ea2a6a
-- title:
--   Long Gaps Between Primes: replaced Residue Weight interval error
-- statement:
--   The replaced weight's second-moment averaging error is at most `16 * D ^ 6 / T`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3159-L3169
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3159-L3169

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.replacedResidueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) (i : Fin k) :
    |integerAverage T (fun n => replacedResidueWeight P k D root i (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => replacedResidueWeight P k D root i t ^ 2)| ≤
        16 * D ^ 6 / T := by sorry
