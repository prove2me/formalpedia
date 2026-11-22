-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_residue_count_error_le_one
-- name    : LongGapsBetweenPrimes.residue_count_error_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:56.486268+00:00
-- url     : https://prove2.me/theorems/9029885b-7532-49e7-81fd-ef8090a95661
-- title:
--   Long Gaps Between Primes: residue count error le one
-- statement:
--   The error of counting one congruence class is at most one.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L712-L723
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L712-L723

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.residue_count_error_le_one {m a : ℕ} (ha : a < m) (T : ℕ) :
    |(∑ n ∈ Finset.range T, residueIndicator m a n) - (T : ℝ) / m| ≤ 1 := by sorry
