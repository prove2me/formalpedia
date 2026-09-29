-- Prove2me | Theorems.Thm_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
-- name    : IntermediateField.isDomain_tensorProduct_of_le_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7714bb97-80d2-5862-9946-f2c01c73479a
-- title:
--   Subfields of κ((q)) remain integral after constant field extension
-- statement:
--   Let $\kappa$ be a field, let $k$ be a field equipped with a $\kappa$-algebra structure (so $k$ is an arbitrary extension field of $\kappa$, with no algebraicity, separability or finiteness assumption), and let $R$ be an intermediate field of the extension $\mathrm{LaurentSeries}\,\kappa / \kappa$, that is, a subfield of the field of formal Laurent series $\kappa((q))$ (Hahn series over $\kappa$ with value group $\mathbb{Z}$) containing the image of $\kappa$. The assertion is that the commutative ring $R \otimes_{\kappa} k$, the tensor product over $\kappa$ of the coercion of $R$ to a type with $k$, is an integral domain: it is nontrivial and has no zero divisors. No hypothesis is placed on $R$ beyond its being an intermediate field of $\kappa((q))/\kappa$, and none on $k$ beyond its being a field extension of $\kappa$.
--
--   This is the statement that a subfield of a field of formal Laurent series stays integral under arbitrary extension of the constant field, i.e. that such a subfield is linearly disjoint from $k$ over $\kappa$ inside $k((q))$. It is used by [`IsDomain.tensorProduct_of_injective_algHom_laurentSeries`](thm.html#IsDomain.tensorProduct_of_injective_algHom_laurentSeries) and, through it, in the analysis of minimal primes on the two-chart model of the modular curve $X_1(p)$, where integrality of coordinate rings must be preserved when the base field is enlarged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IntermediateField.isDomain_tensorProduct_of_le_laurentSeries
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ)) :
    IsDomain (↥R ⊗[κ] k) := by sorry
