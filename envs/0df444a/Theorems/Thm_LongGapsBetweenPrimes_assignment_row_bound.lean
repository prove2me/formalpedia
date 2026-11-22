-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_assignment_row_bound
-- name    : LongGapsBetweenPrimes.assignment_row_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:32:59.118977+00:00
-- url     : https://prove2.me/theorems/d7c25a6b-2b38-4546-b052-f4f9733b08d9
-- title:
--   Long Gaps Between Primes: assignment row bound
-- statement:
--   The cutoff controls the row sums uniformly, independently of the
--   number of auxiliary primes in P.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L655-L706
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L655-L706

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.assignment_row_bound {α : Type*} [Fintype α]
    (size : α → ℕ) {k : ℕ} (hk : 1 ≤ k) (σ : α → Option (Fin k))
    {z D : ℝ} (hz : 1 < z) (hsize : ∀ p, z ≤ (size p : ℝ))
    (hcut : (assignmentProduct size σ : ℝ) ≤ D) :
    (∏ p, localRow (size p) k (σ p)) ≤
      Real.exp ((k : ℝ) * Real.log D / ((z - 1) * Real.log z)) := by sorry
