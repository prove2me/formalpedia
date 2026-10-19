-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_finset_prod_pow_le
-- name    : OAI.PiExponent.FormalInterpolation.ideal_finset_prod_pow_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:40:35.003359+00:00
-- url     : https://prove2.me/theorems/4ad68753-faf8-47bf-a2ae-7edc92020a63
-- title:
--   Power containment for finite products of ideals
-- statement:
--   Pointwise ideal power containments imply the corresponding containment for finite products. This supplies only the aggregation step; it does not assume any separation between centers.

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.ideal_finset_prod_pow_le
    {α R : Type} [Fintype α] [CommSemiring R]
    (A B : α → Ideal R) (r s : Nat)
    (h : ∀ a, A a ^ r ≤ B a ^ s) :
    (∏ a, A a) ^ r ≤ (∏ a, B a) ^ s := by sorry
