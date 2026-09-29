-- Prove2me | Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
-- name    : Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/dd0f605d-0fd4-52e7-9174-751ed9989df7
-- title:
--   Two closed points of an affine variety lie on a curve
-- statement:
--   Let $k$ be an algebraically closed field and let $A$ be a commutative ring which is an integral domain, equipped with a $k$-algebra structure making it of finite type over $k$. Assume that the Krull dimension of $A$, taken in the order-theoretic sense so that $\mathrm{ringKrullDim}\,A$ lies in the extended natural numbers with a bottom element, satisfies $1 \le \mathrm{ringKrullDim}\,A$. Let $\mathfrak m_0$ and $\mathfrak m_1$ be ideals of $A$, each assumed maximal; they are not required to be distinct. The conclusion asserts the existence of an ideal $P$ of $A$ which is prime, satisfies $P \subseteq \mathfrak m_0$ and $P \subseteq \mathfrak m_1$, and is such that the quotient $A / P$ has Krull dimension exactly $1$. Geometrically: the two closed points of $\operatorname{Spec} A$ cut out by $\mathfrak m_0$ and $\mathfrak m_1$ both lie on the irreducible closed subscheme $V(P)$, which is a curve.
--
--   This is the affine, ring-theoretic form of the lemma, used by Mumford in the proof of the theorem of the cube, that any two points of an irreducible variety lie on an irreducible curve through them; the inductive step cuts down the dimension by a hypersurface through both points, for which the companion statement [`Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime`](thm.html#Ideal.exists_mem_and_mem_and_radical_span_singleton_isPrime) produces, when $\mathrm{ringKrullDim}\,A \ge 2$ and $\mathfrak m_0 \ne \mathfrak m_1$, a nonzero $f$ lying in both maximal ideals whose principal ideal has prime radical. It is used in the reduction of membership questions for proper (respectively separated) schemes to the case of smooth proper curves, via [`AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem`](thm.html#AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem) and [`AlgebraicGeometry.mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem`](thm.html#AlgebraicGeometry.mem_of_isSeparated_of_forall_smoothProperCurve_opens_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by sorry
