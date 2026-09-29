-- Prove2me | Theorems.Thm_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
-- name    : GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/7f964255-0e3e-501d-80f0-3f0f1d5b13b3
-- title:
--   Deligne–Serre: conjugacy from equal Frobenius characteristic polynomials
-- statement:
--   Let $\rho,\rho'\colon \operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{GL}_2(\mathbb C)$ be group homomorphisms from the group of field automorphisms of $\overline{\mathbb Q}=\mathtt{AlgebraicClosure }\mathbb Q$ over $\mathbb Q$ into the invertible $2\times 2$ complex matrices, each assumed to factor through a finite level in the sense of [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17): there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that every automorphism fixing $L$ pointwise is sent to the identity matrix. Let $S$ be a finite set of natural numbers, and assume that for every prime $p \notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ lying in the nonunits of $A$, and every $\sigma$ that is a Frobenius at $A$ for $p$ — meaning $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb Q$ and acts on the residue field of $A$ by $x \mapsto x^{p}$ — the characteristic polynomials of the matrices underlying $\rho(\sigma)$ and $\rho'(\sigma)$ agree. Then there exists $P \in \mathrm{GL}_2(\mathbb C)$ with $\rho'(\sigma) = P\,\rho(\sigma)\,P^{-1}$ for all $\sigma$.
--
--   This is the complex two-dimensional case of Lemme 3.2 of Deligne–Serre, with the conclusion that the two representations are isomorphic spelled out as conjugacy of the matrix representations; the proof cites a Frobenius-density statement for open subgroups ([`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`](thm.html#Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen)) together with the corresponding conjugacy result for pairs of representations with finite image ([`Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`](thm.html#Representation.exists_conj_eq_of_charpoly_eq_of_finite_range)). It is used in the construction of the complex Galois representation attached to a weight one form, via [`DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`](thm.html#DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
    (ρ ρ' : Γℚ →* GL (Fin 2) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          ((ρ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
            ((ρ' σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ σ : Γℚ, ρ' σ = P * ρ σ * P⁻¹ := by sorry
