-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residueWeight_interval_error
-- name    : LongGapsBetweenPrimes.residueWeight_interval_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:11.015376+00:00
-- url     : https://prove2.me/theorems/6438a2eb-761b-45bc-bb6a-dd5cfbe128f8
-- title:
--   Long Gaps Between Primes: residue Weight interval error
-- statement:
--   The residue weight's second-moment averaging error is at most `16 * D ^ 6 / T`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2686-L2694
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2686-L2694

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residueWeight_interval_error {P k T : ℕ} (hP : Squarefree P) (hT : 0 < T)
    {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (hcoeff : ∀ d ∈ P.divisors, |coefficient P d| ≤ 1) :
    |integerAverage T (fun n => residueWeight P k D root (residueVector P n) ^ 2) -
      Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2)| ≤ 16 * D ^ 6 / T := by sorry
