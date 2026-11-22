-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_second_moment_le
-- name    : LongGapsBetweenPrimes.replacedResidueWeight_second_moment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:27.038994+00:00
-- url     : https://prove2.me/theorems/febc652e-4888-4b51-989e-adf3577aac41
-- title:
--   Long Gaps Between Primes: replaced Residue Weight second moment le
-- statement:
--   Bound a replaced weight's second moment using tilted and zero coefficient moments.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3108-L3128
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3108-L3128

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.replacedResidueWeight_second_moment_le {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) * coefficientMoment P (2 * β) ^ k +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by sorry
