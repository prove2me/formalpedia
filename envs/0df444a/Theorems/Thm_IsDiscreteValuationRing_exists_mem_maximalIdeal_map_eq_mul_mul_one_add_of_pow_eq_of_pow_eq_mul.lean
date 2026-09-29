-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul
-- name    : IsDiscreteValuationRing.exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/4b5afe16-5958-5586-8dac-86657564c873
-- title:
--   Tame rescaling of n-th roots in a discrete valuation ring
-- statement:
--   Let $A$ be a commutative ring which is a domain and a discrete valuation ring, with maximal ideal $\mathfrak m_A$ (its maximal ideal as a local ring), and let $\sigma : A \to A$ be a ring automorphism which is trivial modulo $\mathfrak m_A$, in the sense that $\sigma(a) - a \in \mathfrak m_A$ for every $a \in A$. Let $n$ be a natural number with $n \ge 1$, let $c \in A$ be non-zero, and let $\pi \in A$ satisfy $\pi^n = c$. Let $\varpi_t \in A$ be an element admitting a unit $u \in A$ with $\varpi_t^{\,n} = c\,u$, and let $\tilde\alpha \in A$ be such that $\sigma(\pi) = \tilde\alpha\,\pi$. The conclusion is that there exists $m \in \mathfrak m_A$ with $$\sigma(\varpi_t) = \tilde\alpha\,\varpi_t\,(1 + m).$$ Thus the same scalar $\tilde\alpha$ that $\sigma$ applies to $\pi$ describes the action of $\sigma$ on any other $n$-th root of $c$ up to a unit, up to an error in $1 + \mathfrak m_A$.
--
--   This is the tame rescaling lemma: an automorphism of a discrete valuation ring that is trivial on the residue field multiplies all $n$-th roots of a fixed element (taken up to units) by one and the same factor modulo $1 + \mathfrak m_A$. It is used in the analysis of the tame inertia action on blow-up charts of Drinfeld level structures, where the automorphism is an inertial generator and $\varpi_t$ is a blow-up parameter whose $n$-th power agrees with $c$ up to a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (σ : A ≃+* A) (hσ : ∀ a : A, σ a - a ∈ IsLocalRing.maximalIdeal A)
    (n : ℕ) (hn : 1 ≤ n) (c : A) (hc : c ≠ 0)
    (π : A) (hπ : π ^ n = c)
    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ n = c * u)
    (αt : A) (hα : σ π = αt * π) :
    ∃ m : A, m ∈ IsLocalRing.maximalIdeal A ∧ σ ϖt = αt * ϖt * (1 + m) := by sorry
