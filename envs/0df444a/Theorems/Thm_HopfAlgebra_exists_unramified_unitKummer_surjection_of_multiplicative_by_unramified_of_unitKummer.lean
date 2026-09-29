-- Prove2me | Theorems.Thm_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
-- name    : HopfAlgebra.exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/25942dba-35aa-50d2-b55c-ffe7cc8fe778
-- title:
--   Unramified level for a unit-Kummer presentation of M
-- statement:
--   Let $p$ be an odd prime, $N$ a natural number, and write $G=\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$ for the group of $\mathbb Q_p$-algebra automorphisms of $\overline{\mathbb Q}_p$, and $I\le G$ for the image under the inclusion of the decomposition subgroup of the inertia subgroup of the valuation subring of $\overline{\mathbb Q}_p$ attached to its canonical valuation. Let $M$ be a finite abelian group with a distributive $G$-action all of whose point stabilisers are open and with $p^N M=0$, let $M_1\le M$ be a $G$-stable subgroup, and let $n:G\to\mathbb N$ satisfy $\tau\xi=\xi^{n(\tau)}$ for every $\xi$ with $\xi^{p^N}=1$. Assume $\tau\cdot y=n(\tau)\,y$ for $\tau\in I$, $y\in M_1$, and $\tau\cdot x-x\in M_1$ for $\tau\in I$, $x\in M$. Fix a primitive $p^N$-th root of unity $\zeta$, and families $u,\beta:\mathrm{Fin}\,t\to\overline{\mathbb Q}_p$ with each $u_i$ of valuation $1$ (a unit for the valuation subring), fixed by $I$, and $\beta_i^{p^N}=u_i$; fix additive endomorphisms $\varphi_i$ of $M$ with image in $M_1$ and vanishing on $M_1$, such that for every $\tau\in I$ acting trivially on the $p^N$-th roots of unity and every $k:\mathrm{Fin}\,t\to\mathbb N$ with $\tau(\beta_i)=\zeta^{k_i}\beta_i$ for all $i$, one has $\tau\cdot x-x=\sum_i k_i\,\varphi_i(x)$ for all $x\in M$. Then there is an intermediate field $K$ of $\overline{\mathbb Q}_p/\mathbb Q_p$, finite over $\mathbb Q_p$, whose fixing subgroup $G_K$ contains $I$, such that every $\sigma\in G_K$ acts on $M_1$ by $y\mapsto n(\sigma)y$ and satisfies $\sigma\cdot x-x\in M_1$ for all $x\in M$, and there are $b,a\in\mathbb N$, families $r,\rho:\mathrm{Fin}\,b\to\mathrm{Fin}\,a\to\overline{\mathbb Q}_p$ and $\kappa:G\to\mathrm{Fin}\,b\to\mathrm{Fin}\,a\to\mathbb N$ with $r_{mk}\in K$, each $r_{mk}$ of valuation $1$, $\rho_{mk}^{p^N}=r_{mk}$, and $\sigma(\rho_{mk})=\zeta^{\kappa(\sigma)_{mk}}\rho_{mk}$ for $\sigma\in G_K$, together with a surjective additive map $\pi:(\mathbb Z/p^N)^b\times(\mathbb Z/p^N)^a\to M$ satisfying $\pi\bigl((n(\sigma)\,i_m+\sum_k\kappa(\sigma)_{mk}\,l_k)_m,\;l\bigr)=\sigma\cdot\pi(i,l)$ for all $\sigma\in G_K$ and all $i,l$.
--
--   This is a step in the local analysis at $p$ of a peu-ramifié Galois module: the unit-Kummer data describing the action of inertia are pushed down to a finite level $K$ unramified over $\mathbb Q_p$ (its fixing subgroup still contains inertia), over which $M$ becomes an equivariant quotient of the points of a product of Kummer carriers with unit radicands. It is used by [`HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level`](thm.html#HopfAlgebra.exists_hopf_points_subquotient_of_unitKummer_over_etale_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem HopfAlgebra.exists_unramified_unitKummer_surjection_of_multiplicative_by_unramified_of_unitKummer
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ)
    (M : Type) [AddCommGroup M] [Finite M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (hM : ∀ x : M, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) x : Set (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])))
    (hpM : ∀ x : M, (p ^ N) • x = 0)
    (M₁ : AddSubgroup M) (hM₁ : ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])), ∀ y ∈ M₁, σ • y ∈ M₁)
    (n : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → ℕ)
    (hn : ∀ (τ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (ξ : AlgebraicClosure ℚ_[p]), ξ ^ p ^ N = 1 → τ ξ = ξ ^ n τ)
    (hmult : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ y ∈ M₁, τ • y = n τ • y)
    (hquot : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ x : M, τ • x - x ∈ M₁)
    (ζ : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ_[p])
    (hu : ∀ i, (padicIntegers p).valuation (u i) = 1)
    (huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (φ : Fin t → (M →+ M)) (hφ₁ : ∀ i x, φ i x ∈ M₁) (hφ₀ : ∀ i, ∀ y ∈ M₁, φ i y = 0)
    (hdec : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], (∀ ξ : AlgebraicClosure ℚ_[p], ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : M, τ • x - x = ∑ i, (k i) • φ i x) :
    ∃ (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])), FiniteDimensional ℚ_[p] ↥K ∧
      (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ K.fixingSubgroup ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ y ∈ M₁, σ • y = n σ • y) ∧
      (∀ σ ∈ K.fixingSubgroup, ∀ x : M, σ • x - x ∈ M₁) ∧
      ∃ (b a : ℕ) (r ρ : Fin b → Fin a → AlgebraicClosure ℚ_[p]) (κ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) → Fin b → Fin a → ℕ),
        (∀ m k, r m k ∈ K) ∧ (∀ m k, (padicIntegers p).valuation (r m k) = 1) ∧ (∀ m k, ρ m k ^ p ^ N = r m k) ∧
        (∀ σ ∈ K.fixingSubgroup, ∀ m k, σ (ρ m k) = ζ ^ κ σ m k * ρ m k) ∧
        ∃ π : (Fin b → ZMod (p ^ N)) × (Fin a → ZMod (p ^ N)) →+ M, Function.Surjective π ∧
          ∀ σ ∈ K.fixingSubgroup, ∀ (i : Fin b → ZMod (p ^ N)) (l : Fin a → ZMod (p ^ N)),
            π (fun m => n σ • i m + ∑ k, κ σ m k • l k, l) = σ • π (i, l) := by sorry
