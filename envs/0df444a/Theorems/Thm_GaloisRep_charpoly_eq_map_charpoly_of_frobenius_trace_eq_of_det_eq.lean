-- Prove2me | Theorems.Thm_GaloisRep_charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq
-- name    : GaloisRep.charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d53e408e-10b2-5fa9-a0a6-0d95f1f29d1a
-- title:
--   Frobenius traces and determinants determine characteristic polynomials
-- statement:
--   Let $k$ and $\kappa$ be fields and $\iota : k \to \kappa$ a ring homomorphism. Let $\bar\rho$ be a residual Galois representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho.\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ that is trivial on every automorphism fixing some finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ pointwise. Let $S$ be a finite set of naturals and $a : \mathbb N \to k$. Assume that for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the characteristic polynomial of $\bar\rho.\rho(\sigma)$ is $X^2 - a(\ell)X + \ell$. Let $\rho$ be a monoid homomorphism from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{GL}_2(\kappa)$, likewise trivial on the automorphisms fixing some finite-dimensional intermediate field pointwise, and assume that for all $\ell$, $A$, $\sigma$ as above one has $\operatorname{tr}\rho(\sigma) = \iota(a(\ell))$ and $\det \rho(\sigma) = \ell$ in $\kappa$. Then for every $\sigma \in \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ the characteristic polynomial of the matrix $\rho(\sigma)$ equals the image under $\iota$ of the characteristic polynomial of $\bar\rho.\rho(\sigma)$.
--
--   This is the Chebotarev comparison used to identify a matrix-valued Galois representation over $\kappa$ with the base change along $\iota$ of a given two-dimensional representation over $k$: agreement of Frobenius characteristic polynomials outside a finite set of primes forces agreement at every element of the Galois group. It is invoked in the construction of auxiliary-level Hecke data, in [`CuspForm.AuxLevel.exists_toML_heckeTL_sub_opAlgHom_pow_mem_of_prime_of_not_dvd`](thm.html#CuspForm.AuxLevel.exists_toML_heckeTL_sub_opAlgHom_pow_mem_of_prime_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

theorem GaloisRep.charpoly_eq_map_charpoly_of_frobenius_trace_eq_of_det_eq
    {k κ : Type} [Field k] [Field κ] (ι : k →+* κ)
    (ρbar : ResidualGaloisRep k) (S : Finset ℕ) (a : ℕ → k)
    (hρbar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (a ℓ) * X + C (ℓ : k))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.trace (ρ σ).val = ι (a ℓ))
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : κ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ σ).val.charpoly = (LinearMap.charpoly (ρbar.ρ σ)).map ι := by sorry
