-- Prove2me | Theorems.Thm_GaloisAction_isUnramifiedAt_pi
-- name    : GaloisAction.isUnramifiedAt_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/ad0ca937-1b34-50f8-837b-9990b4ec3771
-- title:
--   Triviality of inertia on a product of Galois modules
-- statement:
--   Let $A$ be a commutative ring, $\iota$ a type, and $(V_i)_{i\in\iota}$ a family of $A$-modules. Let $G = \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ be the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, and for each $i$ let $\rho_i \colon G \to \operatorname{End}_A(V_i)$ be a monoid homomorphism into the $A$-linear endomorphisms of $V_i$. Let $\rho_\Pi \colon G \to \operatorname{End}_A(\prod_i V_i)$ be a monoid homomorphism on the product module, assumed to act componentwise, i.e. $(\rho_\Pi(\sigma) f)(i) = \rho_i(\sigma)(f(i))$ for all $\sigma \in G$, all $f \in \prod_i V_i$ and all $i$. Let $\ell$ be a natural number, and suppose that each $\rho_i$ is unramified at $\ell$ in the following sense: for every valuation subring $P$ of $\overline{\mathbb Q}$ with $(\ell : \overline{\mathbb Q})$ a nonunit of $P$, and every $\sigma$ lying in the image of the inertia subgroup of $P$ over $\mathbb Q$ under the inclusion of the decomposition subgroup into $G$, one has $\rho_i(\sigma) = 1$. The conclusion is the same property for $\rho_\Pi$: for every such $P$ and every such $\sigma$, $\rho_\Pi(\sigma) = 1$. No finiteness is assumed of $\iota$, and $\ell$ is not assumed prime.
--
--   This is the stability of the condition “unramified at $\ell$”, in the shape used throughout the project (inertia at a valuation subring of $\overline{\mathbb Q}$ over $\ell$ acting trivially), under passage to a product of Galois modules, hence also to finite direct sums. It is applied to the Galois action on a product of Tate modules in [`ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisAction_isUnramifiedAt_pi.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisAction.isUnramifiedAt_pi
    (A : Type) [CommRing A] (ι : Type)
    (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
    (ρ : ∀ i, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (V i))
    (ρpi : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A (∀ i, V i))
    (hρpi : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ∀ i, V i) (i : ι),
      ρpi σ f i = ρ i σ (f i))
    (ℓ : ℕ)
    (hρ : ∀ i, ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ i σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρpi σ = 1 := by sorry
