-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_normalized_bound
-- name    : LongGapsBetweenPrimes.replacedResidueWeight_normalized_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:51.631178+00:00
-- url     : https://prove2.me/theorems/e89b98ba-758c-4b75-a81d-8e3b2a4d68f3
-- title:
--   Long Gaps Between Primes: replaced Residue Weight normalized bound
-- statement:
--   Bound a replaced weight's second moment by `uncoveredBound` times the zero moment.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3219-L3238
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3219-L3238

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.replacedResidueWeight_normalized_bound {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      uncoveredBound k β C M D * coefficientMoment P 0 ^ k := by sorry
