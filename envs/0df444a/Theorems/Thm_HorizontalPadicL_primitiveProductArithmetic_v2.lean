-- Prove2me | Theorems.Thm_HorizontalPadicL_primitiveProductArithmetic_v2
-- name    : HorizontalPadicL.primitiveProductArithmetic_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:10:56.276867+00:00
-- url     : https://prove2.me/theorems/bc3dfa74-6aac-47a0-811a-296e5a079e5a
-- title:
--   Arithmetic of primitive products of Dirichlet characters
-- statement:
--   Primitive-product arithmetic for coprime conductors and coprime orders,
--   including cancellation on primitive characters. This is standard Dirichlet
--   character theory and involves no modular forms or nonvanishing theorem.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Primitive-product arithmetic for coprime conductors and coprime orders,
including cancellation on primitive characters. This is standard Dirichlet
character theory and involves no modular forms or nonvanishing theorem. -/
theorem primitiveProductArithmetic_v2 : PrimitiveProductArithmetic := by
  sorry

end HorizontalPadicL
