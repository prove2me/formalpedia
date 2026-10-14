-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_span_products_mem_representation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.span_products_mem_representation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T18:55:41.193188+00:00
-- url     : https://prove2.me/theorems/8749c72c-dffe-454b-8e27-1a017ee285ee
-- title:
--   Finite representation from a span of ideal products
-- statement:
--   If P lies in the span of products of n ideal elements, then P is a finite sum of coefficients times such products, with every factor in I.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.span_products_mem_representation
    {A : Type*} [CommSemiring A] (I : Ideal A) (n : ℕ) (P : A)
    (hP : P ∈ Ideal.span
      {x : A | ∃ f : Fin n → A, (∀ i, f i ∈ I) ∧ x = ∏ i, f i}) :
    ∃ s : Finset (A × (Fin n → A)),
      P = ∑ z ∈ s, z.1 * ∏ i, z.2 i ∧
      ∀ z ∈ s, ∀ i, z.2 i ∈ I := by sorry
