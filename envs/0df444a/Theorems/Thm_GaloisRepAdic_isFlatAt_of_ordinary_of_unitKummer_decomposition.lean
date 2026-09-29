-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition
-- name    : GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/5a4bccf0-151c-5e12-8c30-fe6ec9f60825
-- title:
--   Unit-Kummer ordinary deformations are flat at p
-- statement:
--   Let $A$ be a finite local commutative ring, $p$ a prime with $p \neq 2$, and $\rho$ a two-dimensional $p$-adic Galois representation in the project's sense: a finite free $A$-module $V$ of rank $2$ with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_A(V)$ which is adically continuous (for each $n$ there is a finite extension $L/\mathbb Q$ in $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m^n V$ for all $v$). Assume `DetIsCyclotomic`: $p$ lies in the maximal ideal of $A$, and whenever $\sigma$ acts on all $p^n$-th roots of unity by $\mu \mapsto \mu^a$, then $\det \rho(\sigma) - a \in (p^n)A$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$, and $b_0, b_1$ an $A$-basis of $V$ such that $A b_0$ is stable under the decomposition subgroup of $P$ and $\rho(\sigma)v - v \in A b_0$ for all $v$ and all $\sigma$ in the inertia subgroup of $P$ (taken as a subgroup of the decomposition group). Let $N$ satisfy $p^N = 0$ in $A$, let $\zeta$ be a primitive $p^N$-th root of unity in $\overline{\mathbb Q}$, and let $u, \beta : \mathrm{Fin}\,t \to \overline{\mathbb Q}$, $a : \mathrm{Fin}\,t \to A$ be such that each $u_i$ has $P$-valuation $1$, each $u_i$ is fixed by inertia, and $\beta_i^{p^N} = u_i$. Assume the inertia cocycle has unit-Kummer shape: for every $\tau$ in inertia acting trivially on the $p^N$-th roots of unity and every $k : \mathrm{Fin}\,t \to \mathbb N$ with $\tau(\beta_i) = \zeta^{k_i}\beta_i$ for all $i$, one has $\rho(\tau)b_1 - b_1 = \bigl(\sum_i k_i a_i\bigr) b_0$. Then $\rho$ satisfies `IsFlatAt p`: the residue field of $A$ is finite, and for every ideal $I$ of $A$ with $A/I$ finite there exist a commutative ring $H$ carrying a Hopf algebra structure over the subring of $\mathbb Q$ of fractions whose denominator is coprime to $p$, finite and flat as a module over that subring and with cocommutative comultiplication, and a bijection $e$ from the set of algebra homomorphisms $H \to \overline{\mathbb Q}$ with its convolution group law onto $V/IV$ with $e(f \ast g) = e(f) + e(g)$, which is Galois-equivariant in the sense that $g = \sigma \circ f$ implies $e(g) = \rho(\sigma)\,e(f)$ for the induced action of $\sigma$ on $V/IV$.
--
--   This is the implication "peu ramifié $\Rightarrow$ flat" for an ordinary two-dimensional representation (Darmon–Diamond–Taylor, Lemma 2.25(c), resting on Raynaud's classification of group schemes of type $(p,\dots,p)$ in the case $e = 1 < p-1$), stated in the form in which the hypothesis is the output of a Kummer decomposition of the inertia cocycle with radicands normalised to units. It is used in the construction of the local invariant at $p$ attached to an ordinary line, via [`GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (b : Module.Basis (Fin 2) A ρ.V)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ b 0)
    (N : ℕ) (hN : (p : A) ^ N = 0)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ) (a : Fin t → A)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) →
        ρ.ρ τ (b 1) - b 1 = (∑ i, (k i) • a i) • b 0) :
    ρ.IsFlatAt p := by sorry
