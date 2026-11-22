-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residueWeight_second_moment
-- name    : LongGapsBetweenPrimes.residueWeight_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:18.041358+00:00
-- url     : https://prove2.me/theorems/ff989706-de38-4f2c-9cc2-874b463bac3d
-- title:
--   Long Gaps Between Primes: residue Weight second moment
-- statement:
--   The tuple weight has the diagonal second moment claimed in (3.9).
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2244-L2268
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2244-L2268

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residueWeight_second_moment {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (ε : ℝ) (hbound : ∀ r : tupleRegion P k D,
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      ε * diagonalMass P k D := by sorry
