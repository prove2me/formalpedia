-- Prove2me | Theorems.Thm_LaurentPolynomial_uniqueFactorizationMonoid
-- name    : LaurentPolynomial.uniqueFactorizationMonoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/901a27c3-0c0d-527a-946c-e4e47bf37b3b
-- title:
--   Laurent polynomials over a UFD form a UFD
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and which is a unique factorisation monoid, i.e. every nonzero non-unit of $R$ admits a factorisation into irreducibles, unique up to associates and reordering (Mathlib's `UniqueFactorizationMonoid`, equivalently: $R$ satisfies the divisor chain condition and every irreducible element is prime). The theorem asserts that the ring $R[T;T^{-1}]$ of Laurent polynomials over $R$ — the Mathlib construction `LaurentPolynomial`, carrying its usual commutative ring structure — is again a unique factorisation monoid. The conclusion is exactly the `UniqueFactorizationMonoid` assertion for $R[T;T^{-1}]$; that this ring is a domain is not part of the stated conclusion, although it is established in the course of the proof. The theorem is stated for $R$ in an arbitrary universe.
--
--   This is the classical statement that unique factorisation passes from a domain $R$ to $R[T,T^{-1}]$, obtained by combining Gauss's theorem for $R[X]$ with stability of unique factorisation under localisation. It is used in the construction of the crossing quotient rings, where it feeds into [`MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed`](thm.html#MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentPolynomial_uniqueFactorizationMonoid.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LaurentPolynomial

universe u

theorem LaurentPolynomial.uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[T;T⁻¹] := by sorry
