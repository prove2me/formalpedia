-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer
-- name    : HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e012fc1f-09c1-55e6-b100-bb338e978e55
-- title:
--   Finite flat ℤₚ-Hopf realisation of a unit-Kummer extension
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N$ be a natural number, and write $G = \operatorname{Aut}_{\mathbb{Q}_p}(\overline{\mathbb{Q}}_p)$ for the group of $\mathbb{Q}_p$-algebra automorphisms of $\overline{\mathbb{Q}}_p =$ `AlgebraicClosure ℚ_[p]`. Let $M$ be a finite abelian group with a distributive $G$-action such that every stabiliser is open (continuity) and $p^N x = 0$ for all $x \in M$, and let $M_1 \le M$ be a $G$-stable subgroup. Let $n : G \to \mathbb{N}$ satisfy $\tau\xi = \xi^{n(\tau)}$ for every $\xi$ with $\xi^{p^N} = 1$ (so $n$ realises the cyclotomic character mod $p^N$). Let $I$ denote the inertia subgroup, namely the image in $G$ of the inertia subgroup of the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of $\overline{\mathbb{Q}}_p$ inside its decomposition subgroup over $\mathbb{Q}_p$. Assume $\tau y = n(\tau)\cdot y$ for $\tau \in I$, $y \in M_1$, and $\tau x - x \in M_1$ for $\tau \in I$, $x \in M$. Let $\zeta$ be a primitive $p^N$-th root of unity, let $t \in \mathbb{N}$ and $u, \beta : \operatorname{Fin} t \to \overline{\mathbb{Q}}_p$ with each $u_i$ of valuation $1$ for [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20), fixed by $I$, and $\beta_i^{p^N} = u_i$. Let $\varphi_i : M \to M$ be additive maps with image in $M_1$ and vanishing on $M_1$, and assume the cocycle decomposition: for $\tau \in I$ acting trivially on $\mu_{p^N}$ and $k : \operatorname{Fin} t \to \mathbb{N}$ with $\tau\beta_i = \zeta^{k_i}\beta_i$, one has $\tau x - x = \sum_i k_i \cdot \varphi_i(x)$ for all $x \in M$. Then there exist a commutative ring $H$ and a Hopf algebra structure on $H$ over $\mathbb{Z}_p$ that is module-finite, flat and cocommutative, together with a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])` to $M$ carrying the convolution product to addition, $e(f \cdot g) = e(f) + e(g)$, and equivariant in the sense that $e(g) = \sigma \cdot e(f)$ whenever $\sigma \in G$ and $g(x) = \sigma(f(x))$ for all $x \in H$.
--
--   This is the 'peu ramifié implies finite flat' construction of Raynaud, in the form of the 'if' direction of Lemma 2.25(c) of Darmon–Diamond–Taylor: a $p$-torsion local Galois module which is an extension of an inertia-trivial quotient by a piece of multiplicative type, with the extension class given by Kummer theory of inertia-fixed units, is the group of $\overline{\mathbb{Q}}_p$-points of a finite flat commutative cocommutative group scheme over $\mathbb{Z}_p$. It is used by [`GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition`](thm.html#GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition) in the analysis of the local behaviour at $p$ of the Galois representations occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer
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
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])) (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ x : H, g x = σ (f x)) → e g = σ • (e f) := by sorry
