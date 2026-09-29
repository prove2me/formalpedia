-- Prove2me | Theorems.Thm_IsDomain_tensorProduct_of_injective_algHom_laurentSeries
-- name    : IsDomain.tensorProduct_of_injective_algHom_laurentSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/2913828c-128f-5de5-b857-aed96a50177a
-- title:
--   Geometric integrality of A-algebras embedding in K((t))
-- statement:
--   Let $A$ be a commutative ring which is a domain, let $K$ be a field which is a field of fractions of $A$ (an $A$-algebra satisfying `IsFractionRing A K`), let $D$ be a nontrivial commutative $A$-algebra, and suppose there is an $A$-algebra homomorphism $\varphi : D \to \mathrm{LaurentSeries}\,K$, the field of formal Laurent series over $K$, which is injective as a function. Let $L$ be a field that is both a $K$-algebra and an $A$-algebra, with the two structures compatible in the sense that $A \to K \to L$ is a scalar tower. Then the commutative ring $L \otimes_A D$ is a domain, i.e. it is nontrivial and has no zero divisors. Thus an $A$-algebra admitting an $A$-embedding into $K(\!(t)\!)$ stays integral after base change to an arbitrary field extension $L$ of $K$: it is geometrically integral over $K$ in this sense. Note that the tensor product is taken over $A$, not over $K$, and that no finiteness hypothesis is placed on $D$ or on $L/K$.
--
--   This is the elementary form of the statement that a variety whose coordinate ring embeds, over the constants, into a field of formal Laurent series over $K$ is geometrically integral, the underlying point being that $K(\!(t)\!)$ and any field extension $L$ of $K$ are linearly disjoint over $K$. It is used to verify integrality of base changes of charts and of quotients by minimal primes in the construction of integral models of modular curves, in particular for full-level and $\Gamma_0$-type moduli data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDomain_tensorProduct_of_injective_algHom_laurentSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsDomain.tensorProduct_of_injective_algHom_laurentSeries
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (D : Type*) [CommRing D] [Nontrivial D] [Algebra A D]
    (φ : D →ₐ[A] LaurentSeries K) (hφ : Function.Injective φ)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    IsDomain (L ⊗[A] D) := by sorry
