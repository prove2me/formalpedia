-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_tateModule_quotient
-- name    : GaloisRepAdic.isUnipotentOnInertiaAt_of_tateModule_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4fdd7f87-0d23-56d2-a9d8-3dcb1d45e210
-- title:
--   Unipotent inertia descends to rank-two quotients of a Tate module
-- statement:
--   Let $M$ be an abelian group carrying a distributive action of $G_{\mathbb Q}=\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$), let $p$ be a prime, and let [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $x:\mathbb N\to M$ with $p^n\cdot x_n=0$ and $p\cdot x_{n+1}=x_n$ for all $n$, a $\mathbb Z_p$-module on which [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) makes $G_{\mathbb Q}$ act $\mathbb Z_p$-linearly by acting termwise. Let $O$ be a commutative local ring and $\rho$ a [`GaloisRepAdic O`](def/GaloisRep_Adic.html#L16), i.e. a free finite $O$-module $V$ with $\operatorname{rank}_O V=2$ together with a monoid homomorphism $\rho\colon G_{\mathbb Q}\to\operatorname{End}_O(V)$ satisfying the adic continuity condition. Let $K$ be a field that is an $O$-algebra and a fraction field of $O$, and also a $\mathbb Z_p$-algebra. Assume given a surjective $K$-linear map $\pi\colon K\otimes_{\mathbb Z_p}\mathrm{Ta}_p M\to K\otimes_O V$ intertwining the base change of [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) with the base change of $\rho$ for every $\sigma\in G_{\mathbb Q}$. Let $q$ be a natural number and assume that for every valuation subring $P$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$ and every $\sigma$ in the image in $G_{\mathbb Q}$ of the inertia subgroup of $P$ over $\mathbb Q$, one has $\sigma(\sigma x-x)=\sigma x-x$ for all $x$ in the Tate module, i.e. $(\sigma-1)^2=0$ there. Then $\rho$ is unipotent on inertia at $q$: for every such $P$ and every such $\sigma$, the characteristic polynomial of $\rho(\sigma)$ on $V$ equals $(X-1)^2$ in $O[X]$.
--
--   This is the transfer step in the analysis of inertia acting on $p$-adic Tate modules: unipotence of échelon two is stable under base change to $K$ and under passage to Galois-equivariant quotients, and in rank two it is equivalent to the characteristic polynomial being $(X-1)^2$. It is used to pass from semistable reduction at $q$, in the form $(\sigma-1)^2=0$ on the Tate module, to the local condition at $q$ for the two-dimensional representation $\rho$, and is cited in the derivation of unipotence on inertia for the representation attached to a newform whose level is exactly divisible by $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_tateModule_quotient.lean

import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem GaloisRepAdic.isUnipotentOnInertiaAt_of_tateModule_quotient
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] (ρ : GaloisRepAdic O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    (π : K ⊗[ℤ_[p]] TateModule p M →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p M),
      π ((TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x))
    (q : ℕ)
    (hT : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ x : TateModule p M,
        TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
            (TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) =
          TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) :
    ρ.IsUnipotentOnInertiaAt q := by sorry
