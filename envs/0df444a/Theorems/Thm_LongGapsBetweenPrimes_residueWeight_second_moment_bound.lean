-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residueWeight_second_moment_bound
-- name    : LongGapsBetweenPrimes.residueWeight_second_moment_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:25.56765+00:00
-- url     : https://prove2.me/theorems/cf2eaf61-0736-4259-96c4-d95d5803af15
-- title:
--   Long Gaps Between Primes: residue Weight second moment bound
-- statement:
--   An explicit exponential bound for the second moment's deviation from the diagonal mass.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2271-L2282
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2271-L2282

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residueWeight_second_moment_bound {P k : ℕ} (hP : Squarefree P) (hk : 1 ≤ k)
    {M D : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      (Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1) * diagonalMass P k D := by sorry
