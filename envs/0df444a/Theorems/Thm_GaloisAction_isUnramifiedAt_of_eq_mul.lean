-- Prove2me | Theorems.Thm_GaloisAction_isUnramifiedAt_of_eq_mul
-- name    : GaloisAction.isUnramifiedAt_of_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/29aa8dc9-a551-59a7-ab14-477fddc5dbdd
-- title:
--   Unramifiedness at ℓ is inherited by pointwise products
-- statement:
--   Let $A$ be a commutative ring and $V$ an $A$-module, and let $\rho_1,\rho_2,\rho$ be three monoid homomorphisms from the group $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to the multiplicative monoid of $A$-linear endomorphisms of $V$. Assume that $\rho$ is the pointwise product of $\rho_1$ and $\rho_2$, that is $\rho(\sigma)=\rho_1(\sigma)\rho_2(\sigma)$ for every $\sigma$. Let $\ell$ be a natural number, and suppose that both $\rho_1$ and $\rho_2$ are unramified at $\ell$ in the following sense: for every valuation subring $P$ of $\overline{\mathbb Q}$ such that the image of $\ell$ in $\overline{\mathbb Q}$ is a non-unit of $P$ (the predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16)), and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$ under the inclusion of the decomposition subgroup (the subgroup [`ValuationSubring.inertiaSubgroupIn`](def/FLTPrelim_Ramification.html#L21)), one has $\rho_1(\sigma)=1$, respectively $\rho_2(\sigma)=1$. The conclusion is that $\rho$ is unramified at $\ell$ in exactly the same sense: $\rho(\sigma)=1$ for every such $P$ and every $\sigma$ in the inertia image. No commutativity of $\rho_1$ with $\rho_2$, and no continuity or finiteness hypothesis, is required.
--
--   This is the elementary closure property stating that a twist of an unramified Galois action by an unramified action — for instance a representation twisted by a character or by a permutation action on geometric components — is again unramified at the prime in question. It is used in the analysis of the Galois action on full-level structures, via [`ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisAction_isUnramifiedAt_of_eq_mul.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisAction.isUnramifiedAt_of_eq_mul
    (A : Type) [CommRing A] (V : Type) [AddCommGroup V] [Module A V]
    (ρ₁ ρ₂ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (hρ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ = ρ₁ σ * ρ₂ σ)
    (ℓ : ℕ)
    (h₁ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₁ σ = 1)
    (h₂ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ₂ σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ σ = 1 := by sorry
