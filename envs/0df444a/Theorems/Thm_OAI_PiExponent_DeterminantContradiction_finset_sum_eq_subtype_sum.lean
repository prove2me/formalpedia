-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_finset_sum_eq_subtype_sum
-- name    : OAI.PiExponent.DeterminantContradiction.finset_sum_eq_subtype_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:27:59.079681+00:00
-- url     : https://prove2.me/theorems/75076d1b-0a04-4467-b044-4178bfc04999
-- title:
--   Convert a finset sum to a sum over its subtype
-- statement:
--   For any finite set and complex-valued function, its finset sum equals the sum indexed by the subtype of elements belonging to that finset.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open Classical
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.finset_sum_eq_subtype_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (g : α → Complex) :
    (∑ a ∈ s, g a) = ∑ c : {a // a ∈ s}, g c.1 := by sorry
