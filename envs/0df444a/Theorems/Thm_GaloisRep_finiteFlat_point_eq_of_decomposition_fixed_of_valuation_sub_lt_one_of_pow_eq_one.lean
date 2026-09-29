-- Prove2me | Theorems.Thm_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
-- name    : GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/70affd8b-318f-5149-a6be-d90a08e7355b
-- title:
--   Injectivity of reduction for ℓ-power points of finite flat group schemes
-- statement:
--   Let $\ell$ be an odd prime (that is, a prime with $\ell \neq 2$) and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ which lies over $\ell$, meaning that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$. Let $H$ be a commutative ring equipped with the structure of a Hopf algebra over the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$ (so over $\mathbb{Z}_{(\ell)}$), such that $H$ is finite and flat as a module over that subring and its comultiplication is cocommutative. Points are taken in `WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)`, the set of $\mathbb{Z}_{(\ell)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ with its convolution group structure. Assume that for some $k \in \mathbb{N}$ every such point $f$ satisfies $f^{\ell^{k}} = 1$. Let $f, g$ be two such points, each fixed by the decomposition subgroup of $A$ over $\mathbb{Q}$ in the sense that $\sigma(f(h)) = f(h)$ and $\sigma(g(h)) = g(h)$ for every $\sigma$ in that subgroup and every $h \in H$, and suppose $A$-valuation of $f(h) - g(h)$ is $< 1$ for all $h \in H$. Then $f = g$.
--
--   This is Raynaud's injectivity of specialisation for points of $\ell$-power order on a finite flat commutative group scheme over $\mathbb{Z}_{(\ell)}$ at an absolutely unramified place above an odd prime $\ell$: points rational over the decomposition group with the same reduction coincide. It is used in the analysis of finite flat models for the Eisenstein quotient of a modular Jacobian, via [`ModularCurve.raynaudFor_of_le_finiteFlat_model_eisensteinQuotient`](thm.html#ModularCurve.raynaudFor_of_le_finiteFlat_model_eisensteinQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H]
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) H] [Module.Flat (GaloisRep.ratLocalizedAt ℓ) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H]
    (k : ℕ) (hord : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), f ^ ℓ ^ k = 1)
    (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (hf : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (f h) = f h)) (hg : (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H, σ (g h) = g h))
    (hfg : ∀ h : H, A.valuation (f h - g h) < 1) :
    f = g := by sorry
