-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq
-- name    : GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2f9c6f25-c337-59e4-939f-88c7fad439b4
-- title:
--   Frobenius-eigenvalue stable line at an unramified prime
-- statement:
--   Let $A$ be a local domain which is a principal ideal ring (so a field or a discrete valuation ring), and let $\rho$ be an object of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ to $\operatorname{End}_A V$, and the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_A^n \cdot V$ for all $v$. Let $q$ be a prime and $P$ a valuation subring of $\overline{\mathbb Q}$ lying over $q$, in the sense that $q$ is a non-unit of $P$. Assume that $\rho(\tau) = 1$ for every $\tau$ in the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$. Let $a, d, \alpha \in A$ with $\alpha^2 - a\alpha + d = 0$, and assume that for every $\sigma$ which is a Frobenius at $P$ for $q$ — that is, $\sigma$ lies in the decomposition subgroup of $P$ and acts on the residue field of $P$ by $x \mapsto x^q$ — the characteristic polynomial of $\rho(\sigma)$ on $V$ is $X^2 - aX + d$. Then there is an $A$-submodule $L \subseteq V$ such that: $L = A\, b_0$ for some $A$-basis $(b_0, b_1)$ of $V$ indexed by $\mathrm{Fin}\,2$; $L$ is stable under $\rho(\sigma)$ for every $\sigma$ in the decomposition subgroup of $P$; $\rho(\tau)v - v \in L$ for every $\tau$ in the image of the inertia subgroup and every $v \in V$; for every Frobenius $\sigma$ at $P$ one has $\rho(\sigma)v - \alpha v \in L$ for all $v \in V$; and for every Frobenius $\sigma$ at $P$ one has $\rho(\sigma)v = (a - \alpha)v$ for all $v \in L$.
--
--   The statement splits a rank-two representation that is unramified at $q$ along a line on which a Frobenius element acts by one chosen root $a-\alpha$ of $X^2-aX+d$, with the complementary root $\alpha$ acting on the free rank-one quotient; it is the local input at an unramified prime for the description of the $q$-adic behaviour of the representations attached to primitive forms. It is used in the construction of the ordinary lines and Frobenius congruences for Galois representations of primitive cusp forms and of points on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ = 1)
    (a d α : A) (hα : α * α - a * α + d = 0)
    (hchar : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C a * X + C d) :
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - α • v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v ∈ L, ρ.ρ σ v = (a - α) • v) := by sorry
