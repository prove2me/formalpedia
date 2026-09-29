-- Prove2me | Theorems.Thm_GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one
-- name    : GaloisRepAdic.ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/c4261599-fc25-562b-b8df-b93b50901543
-- title:
--   Uniqueness of the ordinary line and Frobenius scalar at a ramified place
-- statement:
--   Let $\mathcal O$ be a commutative local domain and let $\rho'$ be an $\mathcal O$-adic Galois representation in the sense of [`GaloisRepAdic 𝒪`](def/GaloisRep_Adic.html#L16): a free finite $\mathcal O$-module $V$ with $\operatorname{rank}_{\mathcal O} V = 2$, a monoid homomorphism $\rho'.\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\operatorname{End}_{\mathcal O}(V)$, subject to the adic continuity condition that for each $n$ some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ has the property that every automorphism fixing it pointwise moves each $v \in V$ by an element of $(\mathfrak m_{\mathcal O}^n) \cdot V$. Let $p$ be a natural number and $P$ a valuation subring of $\overline{\mathbb Q}$; write $D_P$ for its decomposition subgroup over $\mathbb Q$, $I_P$ for the image of its inertia subgroup in the full Galois group, and call $\sigma$ a Frobenius at $p$ when $\sigma \in D_P$ and $\sigma$ acts on the residue field of $P$ by $x \mapsto x^{p}$. Assume given two $\mathcal O$-submodules $L, L' \subseteq V$, each of the form $\mathcal O \cdot b_0$ for the first vector $b_0$ of some $\mathcal O$-basis of $V$ indexed by `Fin 2`, such that $\rho'(\tau)v - v \in L$ and $\rho'(\tau)v - v \in L'$ for all $\tau \in I_P$ and all $v \in V$; and elements $\alpha, \alpha' \in \mathcal O$ with $\rho'(\sigma)v - \alpha v \in L$ for every $\sigma \in D_P$ that is a Frobenius at $p$ and all $v$, and $\rho'(\sigma)v - \alpha' v \in L'$ for every $\sigma$ (ranging over the whole Galois group) that is a Frobenius at $p$ and all $v$. If $\rho'(\tau) \neq 1$ for some $\tau \in I_P$, then $L = L'$, and moreover $\alpha = \alpha'$ provided some $\sigma \in D_P$ is a Frobenius at $p$. The proof uses neither the adic continuity of $\rho'$ nor any arithmetic property of $p$.
--
--   This is the uniqueness assertion accompanying the ordinary filtration at a place where the representation is ramified: an inertia-trivialising free rank-one direct summand, together with the scalar by which Frobenius acts modulo it, is determined by the representation. It is used in the local study of Hecke-algebra representations attached to cusp forms, where the ordinary line and unit root held by the consumer must be identified with those produced from the local behaviour of the associated representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one.lean

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪]
    (ρ' : GaloisRepAdic 𝒪) (p : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ))

    (L : Submodule 𝒪 ρ'.V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L = 𝒪 ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : ρ'.V, ρ'.ρ σ v - α • v ∈ L)

    (L' : Submodule 𝒪 ρ'.V)
    (hL'b : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L' = 𝒪 ∙ b 0)
    (hL'I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ τ v - v ∈ L')
    (α' : 𝒪)
    (hα' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
      ∀ v : ρ'.V, ρ'.ρ σ v - α' • v ∈ L')

    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ τ ≠ 1) :
    L = L' ∧
      ((∃ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p) → α = α') := by sorry
