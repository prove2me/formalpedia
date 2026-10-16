-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_pow_eq_span_fin_products
-- name    : OAI.PiExponent.FormalInterpolation.pow_eq_span_fin_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T06:05:43.852667+00:00
-- url     : https://prove2.me/theorems/214acaf5-7ae5-4824-8e45-55d7866db4ec
-- title:
--   Ideal powers as spans of finite products
-- statement:
--   Every element of the nth power of an ideal lies in the span of products of n ideal elements, with the empty product covering n = 0.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.pow_eq_span_fin_products {α : Type*} [CommSemiring α] (I : Ideal α) (n : ℕ) : I ^ n = Ideal.span {P : α | ∃ s : Fin n → α, (∀ i, s i ∈ I) ∧ P = ∏ i, s i} := by sorry
