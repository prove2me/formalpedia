-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignmentNormalizer_sq
-- name    : LongGapsBetweenPrimes.assignmentNormalizer_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:06.072001+00:00
-- url     : https://prove2.me/theorems/3edbff15-fb1c-4c89-a764-db2c4297c1d2
-- title:
--   Long Gaps Between Primes: assignment Normalizer sq
-- statement:
--   The square of the assignment normalizer equals the assignment variance.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2173-L2181
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2173-L2181

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignmentNormalizer_sq {α : Type*} [Fintype α] (size : α → ℕ)
    (hsize : ∀ p, 1 < size p) {k : ℕ} (σ : α → Option (Fin k)) :
    assignmentNormalizer size σ ^ 2 = assignmentVariance size σ := by sorry
