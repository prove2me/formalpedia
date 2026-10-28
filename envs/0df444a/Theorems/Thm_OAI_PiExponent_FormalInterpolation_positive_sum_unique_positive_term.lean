-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_sum_unique_positive_term
-- name    : OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:21:40.970657+00:00
-- url     : https://prove2.me/theorems/fc322e93-750d-4334-a019-0a573caf1008
-- title:
--   A positive sum with at most one positive term equals that term
-- statement:
--   For a finite family of natural numbers with at most one positive term, a positive sum has exactly one positive term, and that term equals the sum.

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term
    {K : Nat} [Fintype (Fin K)] (f : Fin K → Nat)
    (hunique : ∀ j k : Fin K, j ≠ k → ¬ (0 < f j ∧ 0 < f k))
    (hsum : 0 < ∑ j, f j) :
    ∃ j : Fin K, 0 < f j ∧ f j = ∑ k, f k := by sorry
