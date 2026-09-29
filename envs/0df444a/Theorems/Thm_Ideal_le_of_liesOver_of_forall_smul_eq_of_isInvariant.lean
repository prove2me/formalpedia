-- Prove2me | Theorems.Thm_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant
-- name    : Ideal.le_of_liesOver_of_forall_smul_eq_of_isInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/66621e14-5012-55a4-bc51-9c343ff24164
-- title:
--   G-stable primes are contained in primes over a common base prime
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a finite group acting on $B$ by ring automorphisms in a way that commutes with the $A$-action (so $G$ acts by $A$-algebra automorphisms), and assume `Algebra.IsInvariant A B G`, i.e. every element of $B$ fixed by all of $G$ lies in the image of the structure map $A \to B$. Let $\mathfrak p_0, \mathfrak p_1$ be prime ideals of $B$ that are stable under the (pointwise) action of $G$, in the sense that $g \cdot \mathfrak p_i = \mathfrak p_i$ for every $g \in G$ and $i = 0, 1$. Let $\mathfrak y$ be a prime ideal of $A$ such that the contractions $\mathfrak p_0 \cap A$ and $\mathfrak p_1 \cap A$ (the preimages of $\mathfrak p_0$ and $\mathfrak p_1$ under $A \to B$, written `Ideal.under A`) are both contained in $\mathfrak y$. Finally let $\mathfrak Q$ be a prime ideal of $B$ lying over $\mathfrak y$, i.e. with $\mathfrak Q \cap A = \mathfrak y$. The conclusion is that $\mathfrak p_0 \subseteq \mathfrak Q$ and $\mathfrak p_1 \subseteq \mathfrak Q$.
--
--   This is the standard lifting lemma of the invariant theory of finite group actions: for the finite quotient map $\operatorname{Spec} B \to \operatorname{Spec} A$ attached to $A = B^G$, every point lying over a specialisation of the images of two $G$-stable irreducible closed subsets lies on both of them. It is used in the study of the coordinate charts of the modular curve $X_1(p)$, where it controls which minimal primes of an ideal generated in a chart algebra are contained in a given prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem Ideal.le_of_liesOver_of_forall_smul_eq_of_isInvariant
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (𝔭₀ 𝔭₁ : Ideal B) [𝔭₀.IsPrime] [𝔭₁.IsPrime]
    (h₀ : ∀ g : G, g • 𝔭₀ = 𝔭₀) (h₁ : ∀ g : G, g • 𝔭₁ = 𝔭₁)
    (y : Ideal A) [y.IsPrime] (hy₀ : 𝔭₀.under A ≤ y) (hy₁ : 𝔭₁.under A ≤ y)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.under A = y) :
    𝔭₀ ≤ Q ∧ 𝔭₁ ≤ Q := by sorry
