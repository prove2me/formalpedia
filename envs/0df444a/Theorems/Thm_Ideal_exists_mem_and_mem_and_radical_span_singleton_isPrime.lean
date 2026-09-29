-- Prove2me | Theorems.Thm_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime
-- name    : Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/4c7d48e7-cfc0-5e37-ba0c-593d2694fbc2
-- title:
--   Bertini irreducibility: irreducible hypersurface section through two points
-- statement:
--   Let $k$ be a field that is algebraically closed, and let $A$ be a commutative ring which is an integral domain, equipped with a $k$-algebra structure making it of finite type over $k$ (all of this carried by the standard typeclass assumptions). Assume that the Krull dimension of $A$, taken in the extended ordered value type used by `ringKrullDim`, satisfies $2 \le \operatorname{ringKrullDim} A$. Let $\mathfrak m_0$ and $\mathfrak m_1$ be two ideals of $A$, each assumed maximal, and assume $\mathfrak m_0 \neq \mathfrak m_1$. The conclusion asserts the existence of an element $f \in A$ such that $f \in \mathfrak m_0$, $f \in \mathfrak m_1$, $f \neq 0$, and the radical of the principal ideal $(f) = \operatorname{span}_A\{f\}$ is a prime ideal of $A$. Thus two distinct closed points of an irreducible affine $k$-variety of dimension at least two lie on a common hypersurface section whose underlying closed subset is irreducible, no smoothness or normality hypothesis being imposed on $A$.
--
--   This is the existence form of Bertini's irreducibility theorem in its smoothness-free (Jouanolou) shape, specialised to a linear system of divisors through two prescribed closed points. It feeds [`Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one`](thm.html#Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one), which turns the prime $\sqrt{(f)}$ into a prime ideal contained in both maximal ideals whose quotient has Krull dimension one, i.e. an irreducible curve through the two given points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_mem_and_mem_and_radical_span_singleton_isPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 2 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] (hne : m₀ ≠ m₁) :
    ∃ f : A, f ∈ m₀ ∧ f ∈ m₁ ∧ f ≠ 0 ∧ (Ideal.span {f}).radical.IsPrime := by sorry
