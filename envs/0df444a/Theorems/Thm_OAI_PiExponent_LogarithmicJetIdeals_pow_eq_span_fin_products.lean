-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_pow_eq_span_fin_products
-- name    : OAI.PiExponent.LogarithmicJetIdeals.pow_eq_span_fin_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T18:55:33.542016+00:00
-- url     : https://prove2.me/theorems/a9387f65-14fb-4d42-bd86-698703b3b164
-- title:
--   Ideal powers are spanned by finite products
-- statement:
--   For every natural n, the nth power of an ideal is the span of products of exactly n elements of that ideal. At n = 0, the only product is 1, whose span is the unit ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.pow_eq_span_fin_products
    {A : Type*} [CommSemiring A] (I : Ideal A) (n : ℕ) :
    I ^ n = Ideal.span
      {x : A | ∃ f : Fin n → A, (∀ i, f i ∈ I) ∧ x = ∏ i, f i} := by sorry
