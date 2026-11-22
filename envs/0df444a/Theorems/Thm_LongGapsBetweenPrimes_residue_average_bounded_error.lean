-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residue_average_bounded_error
-- name    : LongGapsBetweenPrimes.residue_average_bounded_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:40.696189+00:00
-- url     : https://prove2.me/theorems/a4b9c170-02db-4174-b84d-774e8438ca65
-- title:
--   Long Gaps Between Primes: residue average bounded error
-- statement:
--   A bounded function of one residue class has interval-average error at most m/T.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2304-L2320
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2304-L2320

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residue_average_bounded_error {m T : ℕ} (hm : 0 < m) (hT : 0 < T)
    (g : Fin m → ℝ) (hg : ∀ a, |g a| ≤ 1) :
    |integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) - Finset.expect Finset.univ g| ≤
      (m : ℝ) / T := by sorry
