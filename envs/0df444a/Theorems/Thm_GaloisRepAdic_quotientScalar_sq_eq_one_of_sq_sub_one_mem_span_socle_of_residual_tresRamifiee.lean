-- Prove2me | Theorems.Thm_GaloisRepAdic_quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee
-- name    : GaloisRepAdic.quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/c8cfb4ce-d637-5ff3-92af-84cf05159034
-- title:
--   Quotient scalars are ± 1 for très ramifiée residual representations
-- statement:
--   Let $p$ be an odd prime, let $B$ be a finite commutative local ring with maximal ideal $\mathfrak m$, and let $\rho$ be an adic Galois representation over $B$: a finite free $B$-module $V$ with $\operatorname{rank}_B V = 2$ together with a monoid homomorphism $\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\operatorname{End}_B V$ which is adically continuous, in the sense that for each $n$ there is a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ whose pointwise stabiliser moves every $v \in V$ only inside $\mathfrak m^n V$. Assume the determinant is cyclotomic at $p$: $p \in \mathfrak m$, and whenever $\sigma$ raises all $p^n$-th roots of unity to the power $a$, then $\det \rho(\sigma) - a \in (p^n)$. Let $L \subseteq V$ be a submodule which is the $B$-span of the first vector of some basis of $V$ indexed by $\mathrm{Fin}\,2$; assume $L$ is stable under the decomposition subgroup of the chosen place $P_0$ of $\overline{\mathbb Q}$ above $p$ (the pullback of the valuation subring of an algebraic closure of $\mathbb Q_p$ along a fixed embedding), and that the inertia subgroup at $P_0$ acts trivially on $V/L$, i.e. $\rho(\sigma)v - v \in L$ for all $v$. Let $t \in \mathfrak m$ satisfy $t\mathfrak m = 0$, and assume that every $\sigma$ in the decomposition group at $P_0$ and every $z \in B$ with $\rho(\sigma)v - z v \in L$ for all $v$ satisfy $z^2 - 1 \in (t)$. Assume further the following très ramifiée property of the residual representation $\rho$ on $\operatorname{ResidueField}(B) \otimes_B V$: for every finite family $u_i$ of elements of $\overline{\mathbb Q}$ of $P_0$-valuation $1$ which are fixed by the inertia subgroup at $P_0$, and every family $\beta_i$ with $\beta_i^p = u_i$, there is an element $\sigma$ of the inertia subgroup at $P_0$ fixing all $p$-th roots of unity and all the $\beta_i$ with residual image $\neq 1$. Then, for any $\sigma$ in the decomposition group at $P_0$ and any $z \in B$ with $\rho(\sigma)v - z v \in L$ for all $v$, one has $z^2 = 1$.
--
--   This is the ring-theoretic heart of the assertion that an ordinary deformation of a très ramifiée residual representation at $p$ is automatically strictly ordinary: the quotient character on $V/L$ can only be deformed in the direction $t$ of the socle if that deformation is trivial, so the unramified quotient character has square exactly $1$. It is used to deduce the strict ordinarity condition from the ordinarity condition for representations with très ramifiée reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee.lean

import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic B) (hdet : ρ.DetIsCyclotomic p)
    (L : Submodule B ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) B ρ.V, L = B ∙ b 0)
    (hLD : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ σ ∈ (padicPlace p).decompositionSubgroup ℚ, ∀ z : B,
      (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) → z * z - 1 ∈ Ideal.span {t})
    (htres : ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧
            ρ.residual.ρ σ ≠ 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ (padicPlace p).decompositionSubgroup ℚ)
    (z : B) (hz : ∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) :
    z * z = 1 := by sorry
