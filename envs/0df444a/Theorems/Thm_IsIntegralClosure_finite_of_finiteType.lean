-- Prove2me | Theorems.Thm_IsIntegralClosure_finite_of_finiteType
-- name    : IsIntegralClosure.finite_of_finiteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/9a74d075-f74a-5f5f-801f-29882692a8bb
-- title:
--   Noether's finiteness theorem for integral closures
-- statement:
--   Let $k$ be a field and $A$ a commutative ring which is an integral domain and a $k$-algebra of finite type (finitely generated as a $k$-algebra). Let $K$ be a field equipped with an $A$-algebra structure making it a fraction field of $A$ (localisation of $A$ at its nonzero elements), and let $L$ be a field which is a $K$-algebra, finite-dimensional as a $K$-vector space, together with an $A$-algebra structure compatible with the tower $A \to K \to L$. Let $C$ be a commutative ring with compatible $A$-algebra and $C$-algebra-of-$L$ structures, i.e. $A \to C \to L$ is a tower, and assume $C$ is an integral closure of $A$ in $L$: the structure map $C \to L$ is injective and its image is exactly the set of elements of $L$ integral over $A$. The conclusion is that $C$ is a finite $A$-module, i.e. finitely generated as a module over $A$. Note that $A$ is not assumed normal, nor $L$ separable over $K$, and $C$ is any ring realising the integral closure rather than a designated subring of $L$.
--
--   This is Emmy Noether's finiteness theorem for integral closures over a finitely generated domain over a field, valid in arbitrary characteristic and without separability hypotheses; the case $L = K$ says that the normalisation of such a domain is a finite module over it. Within this development it supplies the finiteness input for producing, over an integral scheme, a finite morphism with integrally closed stalks, as used by [`AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral`](thm.html#AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegralClosure_finite_of_finiteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegralClosure.finite_of_finiteType
    (k A K L C : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [CommRing C] [Algebra C L] [Algebra A C] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    Module.Finite A C := by sorry
