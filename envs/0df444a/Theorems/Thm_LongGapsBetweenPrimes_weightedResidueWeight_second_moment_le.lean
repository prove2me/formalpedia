-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_weightedResidueWeight_second_moment_le
-- name    : LongGapsBetweenPrimes.weightedResidueWeight_second_moment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:21.292402+00:00
-- url     : https://prove2.me/theorems/35d8b357-eee3-4281-b2c4-ded709a3d28c
-- title:
--   Long Gaps Between Primes: weighted Residue Weight second moment le
-- statement:
--   Bound the weighted second moment by the Gram factor times its diagonal mass.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3012-L3048
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3012-L3048

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.weightedResidueWeight_second_moment_le {P k : ℕ} (hP : Squarefree P)
    {D M : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (b : DivisorTuple P k → ℝ) :
    Finset.expect Finset.univ (fun t => weightedResidueWeight P k D root b t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by sorry
