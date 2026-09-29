-- Prove2me | Theorems.Thm_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
-- name    : GaloisRepAdic.false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/26c359a2-4476-5196-bc32-61d9bc4944ea
-- title:
--   Très ramifiée witness contradicts inertia acting trivially mod 𝔪
-- statement:
--   Let $B$ be a commutative local ring with maximal ideal $\mathfrak m$, let $p$ be a prime, and let $\rho$ be an adic Galois representation over $B$: a finite free $B$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_B(V)$ satisfying the adic continuity condition of [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9). Let $\beta \in \overline{\mathbb Q}_p$ satisfy $\beta^p = 1+p$. Assume two things. First (`hsplit`): for every $\tau$ in the inertia subgroup of the valuation ring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) over $\mathbb Q_p$ (the image in $\mathrm{Aut}(\overline{\mathbb Q}_p/\mathbb Q_p)$ of the inertia subgroup inside the decomposition subgroup) such that $\tau$ fixes every $\xi$ with $\xi^p=1$ and fixes $\beta$, the element $\rho.\rho(\mathrm{localGaloisToGlobal}(p,\tau))$ satisfies $\rho.\rho(\cdot)v - v \in \mathfrak m \cdot V$ for all $v \in V$. Second (`htres`): for every $n$ and all families $u, \beta' : \mathrm{Fin}\,n \to \overline{\mathbb Q}$ with each $u_i$ of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25)-valuation $1$, each $u_i$ fixed by the inertia subgroup of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) over $\mathbb Q$, and $\beta'^p_i = u_i$, there exists $\sigma$ in that inertia subgroup fixing all $p$-th roots of unity, fixing each $\beta'_i$, and with residual image $\rho.\mathrm{residual}.\rho(\sigma) \neq 1$, where the residual representation is the base change of $\rho$ along $B \to B/\mathfrak m$. The conclusion is `False`: the two hypotheses are incompatible.
--
--   This is the incompatibility, at the prime $p$, between the residual representation being très ramifiée in the unit-Kummer sense of Serre (the witness-producing hypothesis `htres`) and its being trivial modulo $\mathfrak m$ on the inertia elements that fix $\mu_p$ and a $p$-th root of $1+p$. It feeds the deduction [`GaloisRepAdic.quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee`](thm.html#GaloisRepAdic.quotientScalar_sq_eq_one_of_sq_sub_one_mem_span_socle_of_residual_tresRamifiee).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.false_of_residual_tresRamifiee_of_root_one_add_prime_inertia_sub_mem
    {B : Type} [CommRing B] [IsLocalRing B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (β : PadicAlgCl p) (hβ : β ^ p = 1 + (p : PadicAlgCl p))
    (hsplit : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        (∀ ξ : PadicAlgCl p, ξ ^ p = 1 → τ ξ = ξ) → τ β = β →
          ∀ v : ρ.V, ρ.ρ (localGaloisToGlobal p τ) v - v ∈
            (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B ρ.V))
    (htres : ∀ (n : ℕ) (u β : Fin n → AlgebraicClosure ℚ),
        (∀ i, (padicPlace p).valuation (u i) = 1) →
        (∀ i, ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, σ (u i) = u i) →
        (∀ i, β i ^ p = u i) →
        ∃ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ) ∧ (∀ i, σ (β i) = β i) ∧
            ρ.residual.ρ σ ≠ 1) :
    False := by sorry
