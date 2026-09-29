-- Prove2me | Theorems.Thm_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
-- name    : GaloisRepAdic.residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/bbdfc5d7-96d7-582e-9328-677055258100
-- title:
--   Residual identification and determinant of an adic lift
-- statement:
--   Let $\mathcal O$ be a characteristic-zero discrete valuation domain, $p$ a prime with $p \in \mathfrak m_{\mathcal O}$, and let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $\mathcal O$: a free finite $\mathcal O$-module $V$ with $\operatorname{rank} 2$, a monoid homomorphism $\sigma \mapsto \rho(\sigma)$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_{\mathcal O}(V)$, adically continuous in the sense that for each $n$ some finite subextension $L/\mathbb Q$ of $\overline{\mathbb Q}$ has $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v$ and all $\sigma$ fixing $L$ pointwise. Let $\bar\rho$ be a two-dimensional representation over a field $k$ factoring through a finite level, absolutely irreducible (irreducible after base change to $\overline{k}$), and $\psi : k \to \mathcal O/\mathfrak m$ a ring homomorphism. Let $L \ge 1$, let $\kappa : \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q}) \to (\mathbb Z/L)^{\times}$ satisfy $\sigma\mu = \mu^{\kappa(\sigma)}$ for all $\mu$ with $\mu^L = 1$, and let $\chi : (\mathbb Z/L)^{\times} \to \mathcal O^{\times}$ be a homomorphism; assume $p \ne 2$, or else that $\chi(u) \equiv 1 \bmod \mathfrak m$ for every $u$. Let $S_0$ be a finite set of naturals and, for each prime $\ell \notin S_0$, let $a_\ell \in \mathcal O$ and $\bar a_\ell \in k$ satisfy $a_\ell \bmod \mathfrak m = \psi(\bar a_\ell)$. Assume that for every prime $\ell \notin S_0$, every valuation subring $A$ of $\overline{\mathbb Q}$ in which $\ell$ is a non-unit, and every $\sigma$ in the decomposition group of $A$ acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\operatorname{charpoly}(\rho(\sigma)) = X^2 - a_\ell X + \chi(\kappa(\sigma))\,\ell$ and $\operatorname{charpoly}(\bar\rho(\sigma)) = X^2 - \bar a_\ell X + \ell$ in $k[X]$. The conclusion is threefold: the reduction $(\mathcal O/\mathfrak m) \otimes_{\mathcal O} V$ of $\rho$, with the base-changed action, is isomorphic as a representation to the base change of $\bar\rho$ along $\psi$; $\chi(\kappa(\sigma)) \equiv 1 \bmod \mathfrak m$ for every $\sigma$; and for all $n \in \mathbb N$, all $\sigma$ and all $b \in \mathbb N$ such that $\sigma\mu = \mu^{b}$ for every $\mu$ with $\mu^{p^n} = 1$, one has $\det(\rho(\sigma)) - b\,\chi(\kappa(\sigma)) \in (p^n)\mathcal O$.
--
--   This is the residual comparison step for a two-dimensional $\mathcal O$-adic representation whose Frobenius characteristic polynomials are $X^2 - a_\ell X + \chi(\kappa(\sigma))\ell$: it identifies the reduction with a given absolutely irreducible residual representation, shows the nebentypus character has trivial reduction, and pins down the determinant as the product of the cyclotomic character and the nebentypus modulo powers of $p$. It is used for the representations attached to points of Hecke rings at non-Eisenstein maximal ideals in the Taylor–Wiles argument, and is cited by the construction of such adic representations from algebra homomorphisms on Hecke rings and by the vanishing of the diamond operators on the relevant residual data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem GaloisRepAdic.residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (p : ℕ) [Fact p.Prime] (hpO : (p : O) ∈ maximalIdeal O)
    (ρ : GaloisRepAdic O)
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (ψ : k →+* ResidueField O)
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (χ : (ZMod L)ˣ →* Oˣ)
    (h2 : p ≠ 2 ∨ ∀ u : (ZMod L)ˣ, residue O (χ u) = 1)
    (S₀ : Finset ℕ) (a : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → O) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hred : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀), residue O (a ℓ hℓ hℓS) = ψ (abar ℓ hℓ hℓS))
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C (a ℓ hℓ hℓS) * X + C ((χ (κ σ) : O) * (ℓ : O)))
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k)) :
    ρ.residual.IsEquiv (ρbar.baseChangeAlong ψ) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, residue O (χ (κ σ)) = 1) ∧
    (∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ b) →
        LinearMap.det (ρ.ρ σ) - (b : O) * (χ (κ σ) : O) ∈ Ideal.span {((p ^ n : ℕ) : O)}) := by sorry
