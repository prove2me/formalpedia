-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignment_row_bound_all
-- name    : LongGapsBetweenPrimes.assignment_row_bound_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:12.052112+00:00
-- url     : https://prove2.me/theorems/a043238b-2742-4bd9-a749-d1dfdd2f3922
-- title:
--   Long Gaps Between Primes: assignment row bound all
-- statement:
--   An exponential assignment row bound valid for every tuple length.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2975-L2986
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2975-L2986

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignment_row_bound_all {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (σ : α → Option (Fin k))
    {M D : ℝ} (hM : 1 < M) (hsize : ∀ p, M ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) := by sorry
