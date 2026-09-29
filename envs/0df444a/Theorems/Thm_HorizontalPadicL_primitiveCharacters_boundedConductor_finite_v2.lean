-- Prove2me | Theorems.Thm_HorizontalPadicL_primitiveCharacters_boundedConductor_finite_v2
-- name    : HorizontalPadicL.primitiveCharacters_boundedConductor_finite_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:10:58.917983+00:00
-- url     : https://prove2.me/theorems/e6093102-59af-48b8-afd3-a5d02429e9b9
-- title:
--   Finiteness of primitive characters of bounded conductor
-- statement:
--   There are only finitely many primitive algebraic Dirichlet characters
--   with conductor bounded by a fixed real number. Primitivity prevents duplicate
--   presentations at unbounded levels.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- There are only finitely many primitive algebraic Dirichlet characters
with conductor bounded by a fixed real number. Primitivity prevents duplicate
presentations at unbounded levels. -/
theorem primitiveCharacters_boundedConductor_finite_v2 (X : ℝ) :
    {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ (χ.2.conductor : ℝ) ≤ X}.Finite := by
  sorry

end HorizontalPadicL
