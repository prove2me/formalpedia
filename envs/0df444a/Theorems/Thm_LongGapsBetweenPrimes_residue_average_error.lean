-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residue_average_error
-- name    : LongGapsBetweenPrimes.residue_average_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:08.401216+00:00
-- url     : https://prove2.me/theorems/c6225774-b7a5-4c54-a0d4-f938dae3c988
-- title:
--   Long Gaps Between Primes: residue average error
-- statement:
--   A residue class has frequency error at most `1 / T` on an interval of length `T`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L726-L734
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L726-L734

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residue_average_error {m a T : ℕ} (ha : a < m) (hT : 0 < T) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) / (T : ℝ) - 1 / (m : ℝ)| ≤
      1 / (T : ℝ) := by sorry
