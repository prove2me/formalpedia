-- Prove2me | Theorems.Thm_GaloisRep_exists_stableLine_of_conj_map
-- name    : GaloisRep.exists_stableLine_of_conj_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/29525397-3882-5278-92f3-05ff66176de5
-- title:
--   Descent of an ordinary stable-line package along conjugation
-- statement:
--   Let $p$ be a prime, let $e \colon F \to F'$ be a ring homomorphism of fields, and let $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(F)$ be a group homomorphism (with $\overline{\mathbb{Q}}$ the algebraic closure of $\mathbb{Q}$) that factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $[L:\mathbb{Q}]$ finite such that $\rho(\sigma)=1$ for every $\sigma$ fixing $L$ pointwise. Let $\rho' \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(F')$ be a homomorphism and $g \in \mathrm{GL}_2(F')$ with $\rho'(\sigma) = g\, e(\rho(\sigma))\, g^{-1}$ for all $\sigma$, where $e$ is applied entrywise. Fix $k_n \in \mathbb{N}$, $a_p \in F$, and a valuation subring $P$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $P$; write $D_P$ for its decomposition subgroup over $\mathbb{Q}$ and $I_P$ for the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of its inertia subgroup, and say $\sigma$ is a Frobenius at $P$ if $\sigma \in D_P$ and $\sigma$ acts on the residue field of $P$ by $x \mapsto x^{p}$. Assume there is a nonzero $v' \in (F')^{2}$ such that: $\rho'(\sigma)v' \in F'v'$ for all $\sigma \in D_P$; $\rho'(\sigma)w - w \in F'v'$ for all $\sigma \in I_P$ and all $w \in (F')^{2}$; $\rho'(\sigma)w - e(a_p)w \in F'v'$ for every Frobenius $\sigma$ at $P$ and all $w$; and $\rho'(\sigma)v' = a^{\,k_n-1}v'$ whenever $\sigma \in I_P$ and $a \in \mathbb{N}$ satisfy $\sigma\mu = \mu^{a}$ for all $\mu \in \overline{\mathbb{Q}}$ with $\mu^{p}=1$. Then there is a nonzero $v \in F^{2}$ satisfying the four corresponding conditions for $\rho$ over $F$, with the line $Fv$, the scalar $a_p$ in place of $e(a_p)$, and $a^{\,k_n-1}$ computed in $F$.
--
--   This is the descent step for the ordinary (or stable-line) local condition at $p$: a package consisting of a $D_P$-stable line, unipotence of inertia modulo that line, the Frobenius eigenvalue condition with trace $a_p$, and the prescribed action of inertia on the line, is transported from a representation over a larger field $F'$ back to a representation over $F$ whose scalar extension it is, up to conjugation. It is used in the verification of the local conditions at $p$ for the Galois representations attached to the relevant modular forms, being cited in the construction of stable lines for the $\theta$-cycle arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_stableLine_of_conj_map.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_stableLine_of_conj_map
    (p : ℕ) [Fact p.Prime] {F F' : Type} [Field F] [Field F'] (e : F →+* F')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F')
    (g : GL (Fin 2) F') (hconj : ∀ σ, (ρ' σ).val = g.val * (ρ σ).val.map e * (g⁻¹).val)
    (kn : ℕ) (ap : F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (h' : ∃ v' : Fin 2 → F', v' ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ' σ).val v' ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - w ∈ F' ∙ v') ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - e ap • w ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ' σ).val v' = ((a : F') ^ (kn - 1)) • v')) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ σ).val v ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - w ∈ F ∙ v) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - ap • w ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ σ).val v = ((a : F) ^ (kn - 1)) • v) := by sorry
