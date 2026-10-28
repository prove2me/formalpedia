-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_sum_unique_positive_term_v2
-- name    : OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:27:06.605495+00:00
-- url     : https://prove2.me/theorems/4a0502a2-7fb3-4ebd-8d08-83d1c958dcf2
-- title:
--   A positive finite sum with at most one positive term equals that term
-- statement:
--   For a finite family of natural numbers with at most one positive term, a positive sum has a positive term equal to the whole sum. This removes the final finite arithmetic selection from the parent. Prove by induction on the finite index set, or select a positive summand and use exclusivity to show every other summand is zero.

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.positive_sum_unique_positive_term_v2
    {K : Nat} [Fintype (Fin K)] (f : Fin K → Nat)
    (hunique : ∀ j k : Fin K, j ≠ k → ¬ (0 < f j ∧ 0 < f k))
    (hsum : 0 < ∑ j, f j) :
    ∃ j : Fin K, 0 < f j ∧ f j = ∑ k, f k := by sorry
