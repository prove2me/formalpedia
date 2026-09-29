-- Prove2me | Theorems.Thm_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
-- name    : IsLocalRing.exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c95de43a-546a-513f-8de2-9793051f0d86
-- title:
--   Truncated monomial expansion modulo an ideal in a local ring
-- statement:
--   Let $W$ and $R$ be commutative rings with $R$ local and equipped with a $W$-algebra structure. Suppose given two elements $y_0, y_1 \in R$ whose generated ideal is the maximal ideal, i.e. $\mathfrak{m}_R = (y_0, y_1)$, and suppose that the residue map is surjective on $W$-constants in the sense that for every $r \in R$ there exists $w \in W$ with $r - \varphi(w) \in \mathfrak{m}_R$, where $\varphi$ denotes the structure map $W \to R$. Let $J$ be an ideal of $R$ and $D$ a natural number such that $y_0^D \in J$ and $y_1^D \in J$, and let $r \in R$. The conclusion is the existence of a family of coefficients $c : \mathbb{N} \times \mathbb{N} \to W$ such that
--   $$r - \sum_{(a,b) \in [0,D) \times [0,D)} \varphi(c_{(a,b)})\, y_0^{a} y_1^{b} \in J,$$
--   the sum being taken over the product of the ranges of $D$ with itself; that is, $r$ is congruent modulo $J$ to a $W$-linear combination of the $D^2$ monomials $y_0^a y_1^b$ with $a, b < D$. No completeness, Noetherian or finiteness assumption is imposed; note that $D = 0$ forces $J = R$ and the statement is then vacuous.
--
--   The statement expresses that $R/J$ is generated as a $W$-module by the $D^2$ truncated monomials $y_0^a y_1^b$, $a,b < D$, hence is a finite $W$-module. It is used in the proof of finiteness of a Drinfeld basis deformation situation over a Lubin–Tate base, where the two coordinates of a formal group law supply $y_0, y_1$ and $J$ contains a power of each.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
    {W R : Type*} [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (y₀ y₁ : R) (hmax : maximalIdeal R = Ideal.span {y₀, y₁})
    (hres : ∀ r : R, ∃ w : W, r - algebraMap W R w ∈ maximalIdeal R)
    (J : Ideal R) (D : ℕ) (h₀ : y₀ ^ D ∈ J) (h₁ : y₁ ^ D ∈ J) (r : R) :
    ∃ c : ℕ × ℕ → W,
      r - ∑ p ∈ Finset.range D ×ˢ Finset.range D, algebraMap W R (c p) * (y₀ ^ p.1 * y₁ ^ p.2) ∈ J := by sorry
