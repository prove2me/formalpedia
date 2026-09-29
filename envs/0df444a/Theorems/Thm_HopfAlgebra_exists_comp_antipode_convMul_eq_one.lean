-- Prove2me | Theorems.Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one
-- name    : HopfAlgebra.exists_comp_antipode_convMul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/1ffa53b0-0363-58bd-9355-844b755f642e
-- title:
--   L-points of a commutative Hopf algebra are convolution-invertible
-- statement:
--   Let $K$ be a commutative ring, $A$ a commutative ring carrying a Hopf algebra structure over $K$, and $L$ a commutative $K$-algebra; let $\nu \colon A \to L$ be a $K$-algebra homomorphism, i.e. an $L$-valued point of $\operatorname{Spec} A$. The assertion is that there exists a $K$-algebra homomorphism $\nu' \colon A \to L$ with two properties. First, the underlying $K$-linear map of $\nu'$ is the composite of the antipode $S$ of $A$ with the linear map underlying $\nu$, that is $\nu' = \nu \circ S$ as linear maps (hence also as functions). Second, in the convolution monoid structure that `WithConv` puts on $A \to_{\mathrm{alg}[K]} L$ — whose product of $\mu,\nu$ is $a \mapsto (\mu \otimes \nu)(\Delta a)$ multiplied out in $L$, and whose unit is the composite of the counit with the structure map $K \to L$ — the images of $\nu'$ and $\nu$ are two-sided inverses: both $\nu' \star \nu = 1$ and $\nu \star \nu' = 1$ hold. In particular $\nu$ is a unit in this monoid.
--
--   This is the standard fact that, for a commutative Hopf algebra, the $L$-points form a group rather than merely a monoid under convolution, the inverse of a point being its precomposition with the antipode. It is used in the treatment of points of Weil restrictions and of Hopf-algebra quotients of monoid algebras occurring later in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem HopfAlgebra.exists_comp_antipode_convMul_eq_one
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
    ∃ ν' : A →ₐ[K] L, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
      WithConv.toConv ν' * WithConv.toConv ν = 1 ∧ WithConv.toConv ν * WithConv.toConv ν' = 1 := by sorry
