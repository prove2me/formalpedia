-- Prove2me | Theorems.Thm_MazurTransfer_affine_open_chart_function_field_is_fraction_ring
-- name    : MazurTransfer.affine_open_chart_function_field_is_fraction_ring
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T13:23:08.769158+00:00
-- url     : https://prove2.me/theorems/6fad0309-b4d5-42a9-8c0c-569854845e0e
-- title:
--   An integral affine chart is a fraction-ring base for the actual scheme function field
-- statement:
--   For an integral scheme $X$ and an open immersion $j:\operatorname{Spec}A\to X$, where $A$ is a domain, there is an injective ring homomorphism $A\to K(X)$ that makes the existing scheme function field $K(X)$ a fraction field of $A$. The proof constructs this homomorphism from the stalk isomorphism of $j$ at the generic point. No field equivalence is assumed as an input. This supplies the actual reciprocal-chart and infinity-local-ring embeddings used in the order-thirteen Pell divisor computation.
-- source:
--   Owned MazurTheorem integration lemma using Mathlib algebraic geometry and fraction-ring APIs; Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474. The named downstream consumer is the literal order-thirteen curve Pell function in its scheme function field.

import Mathlib
open AlgebraicGeometry CategoryTheory
universe u

theorem MazurTransfer.affine_open_chart_function_field_is_fraction_ring
    (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j] :
    ∃ φ : A →+* X.functionField,
      Function.Injective φ ∧ (letI := φ.toAlgebra; IsFractionRing A X.functionField) := by sorry
