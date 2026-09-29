-- Prove2me | Theorems.Thm_GaloisAction_isUnramifiedAt_of_injective_of_map_apply
-- name    : GaloisAction.isUnramifiedAt_of_injective_of_map_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/aceaadd6-c994-57a2-8747-e1c4af1ed6d8
-- title:
--   Unramifiedness descends along injective equivariant maps
-- statement:
--   Let $A$ be a commutative ring and let $V$ and $W$ be $A$-modules, each equipped with a monoid homomorphism from $G = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) = (\mathrm{AlgebraicClosure}\ \mathbb Q \simeq_{\mathbb Q} \mathrm{AlgebraicClosure}\ \mathbb Q)$ to its $A$-linear endomorphism monoid, say $\rho$ on $V$ and $\rho_W$ on $W$. Let $f \colon W \to V$ be an injective $A$-linear map intertwining the two actions, i.e. $f(\rho_W(\sigma) w) = \rho(\sigma)(f(w))$ for all $\sigma \in G$ and $w \in W$. Let $\ell$ be a natural number, and assume that $\rho$ is unramified at $\ell$ in the following sense: for every valuation subring $P$ of $\overline{\mathbb Q}$ such that the image of $\ell$ lies in the nonunits of $P$, and every $\sigma$ in the image in $G$ of the inertia subgroup of $P$ over $\mathbb Q$ (transported along the inclusion of the decomposition subgroup into $G$), one has $\rho(\sigma) = 1$. The conclusion is the same assertion for $\rho_W$: for every such valuation subring $P$ and every $\sigma$ in the image of its inertia subgroup, $\rho_W(\sigma) = 1$.
--
--   This is the elementary closure property that being unramified at a prime passes from a representation to any subrepresentation, stated for an arbitrary injective equivariant $A$-linear map so that it covers a stable submodule with its restricted action, a lattice inside a representation, or a constituent cut out inside a larger Tate module. It is used in the study of the Galois action on torsion of elliptic curves, where it supplies triviality of inertia on a piece of a Tate module from triviality on the ambient module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisAction_isUnramifiedAt_of_injective_of_map_apply.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisAction.isUnramifiedAt_of_injective_of_map_apply
    (A : Type) [CommRing A]
    (V : Type) [AddCommGroup V] [Module A V] (W : Type) [AddCommGroup W] [Module A W]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (ρW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A W)
    (f : W →ₗ[A] V) (hf : Function.Injective f)
    (hfρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : W), f (ρW σ w) = ρ σ (f w))
    (ℓ : ℕ)
    (hρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ σ = 1) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρW σ = 1 := by sorry
