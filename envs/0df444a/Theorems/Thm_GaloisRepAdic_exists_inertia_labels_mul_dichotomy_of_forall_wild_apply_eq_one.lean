-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
-- name    : GaloisRepAdic.exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/7b6970eb-3b08-5d2e-b1e1-c55f1151fb32
-- title:
--   Multiplicative inertia labels for a tame rank-two representation
-- statement:
--   Let $O'$ be a local commutative ring and let $\rho$ be a [`GaloisRepAdic O'`](def/GaloisRep_Adic.html#L16), that is: a finite free $O'$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb Q$, to $\operatorname{End}_{O'}(V)$, subject to the adic continuity condition that for each $n$ some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ has the property that every automorphism fixing it pointwise acts on $V$ trivially modulo $\mathfrak m_{O'}^n V$. Let $q$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $P$; write $I_P$ for the inertia subgroup of $P$ over $\mathbb Q$, viewed inside the full Galois group via the decomposition subgroup. Assume $\rho$ is tame at $P$: every $\sigma \in I_P$ with $\sigma z \cdot z^{-1} - 1$ a nonunit of $P$ for all $z \neq 0$ satisfies $\rho.\rho\,\sigma = 1$. Let $j \colon O' \to O''$ be a ring homomorphism into a domain over which all inertial characteristic polynomials split, i.e. for each $\sigma \in I_P$ the image under $j$ of $\operatorname{charpoly}(\rho.\rho\,\sigma)$ equals $(X - \alpha)(X - \beta)$ for some $\alpha, \beta \in O''$. Then there exist functions $a, b$ from the Galois group to $(O'')^{\times}$ such that for all $\sigma, \tau \in I_P$: the image of $\operatorname{charpoly}(\rho.\rho\,\sigma)$ under $j$ is $(X - a_\sigma)(X - b_\sigma)$; $a_{\sigma\tau} = a_\sigma a_\tau$ and $b_{\sigma\tau} = b_\sigma b_\tau$; $a_\sigma^{q^2-1} = b_\sigma^{q^2-1} = 1$; either $a_\sigma^{q-1} = b_\sigma^{q-1} = 1$ for all $\sigma \in I_P$, or $b_\sigma = a_\sigma^{q}$ and $a_\sigma = b_\sigma^{q}$ for all $\sigma \in I_P$; and $a_\sigma = b_\sigma = 1$ for every wild $\sigma \in I_P$, i.e. one with $\sigma z \cdot z^{-1} - 1$ a nonunit of $P$ for all $z \neq 0$.
--
--   This is the standard description of the action of tame inertia at $q$ on a rank-two representation: the eigenvalue labels are characters of $I_P$ of order dividing $q^2-1$, and either both are valued in the $(q-1)$-st roots of unity (the split case) or they are exchanged by raising to the $q$-th power (the nonsplit case). It is used in the analysis of the local behaviour of newform Galois representations at $q$, in the lemmas on cuspidal type and unipotence on inertia that feed the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem GaloisRepAdic.exists_inertia_labels_mul_dichotomy_of_forall_wild_apply_eq_one
    {O' : Type} [CommRing O'] [IsLocalRing O'] (ρ : GaloisRepAdic O')
    {q : ℕ} [Fact q.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (htame : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ P.inertiaSubgroupIn ℚ →
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → ρ.ρ σ = 1)
    {O'' : Type} [CommRing O''] [IsDomain O''] (j : O' →+* O'')
    (hsplit : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ α β : O'',
      (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C α) * (X - C β)) :
    ∃ a b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ,
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a σ : O''ˣ) : O'')) * (X - C ((b σ : O''ˣ) : O''))) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
        a (σ * τ) = a σ * a τ ∧ b (σ * τ) = b σ * b τ) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1 ∧ b σ ^ (q ^ 2 - 1) = 1) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q - 1) = 1 ∧ b σ ^ (q - 1) = 1) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, b σ = a σ ^ q ∧ a σ = b σ ^ q)) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ,
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) → a σ = 1 ∧ b σ = 1) := by sorry
