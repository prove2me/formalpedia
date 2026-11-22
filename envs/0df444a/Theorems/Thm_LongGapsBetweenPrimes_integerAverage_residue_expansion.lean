-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_integerAverage_residue_expansion
-- name    : LongGapsBetweenPrimes.integerAverage_residue_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:52.108844+00:00
-- url     : https://prove2.me/theorems/2435b150-ffb3-4b58-aeed-0809633989a9
-- title:
--   Long Gaps Between Primes: integer Average residue expansion
-- statement:
--   Express a periodic average using the frequencies of its residue classes.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2294-L2301
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2294-L2301

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.integerAverage_residue_expansion {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (T : ℕ) :
    integerAverage T (fun n => g ⟨n % m, Nat.mod_lt n hm⟩) =
      ∑ a : Fin m, g a * ((∑ n ∈ Finset.range T, residueIndicator m a.val n) / T) := by sorry
