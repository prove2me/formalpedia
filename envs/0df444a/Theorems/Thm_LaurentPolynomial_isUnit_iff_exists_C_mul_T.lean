-- Prove2me | Theorems.Thm_LaurentPolynomial_isUnit_iff_exists_C_mul_T
-- name    : LaurentPolynomial.isUnit_iff_exists_C_mul_T
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b04eb14b-7d81-5b93-b40e-2fad0bab74b0
-- title:
--   Units of R[T;T⁻¹] over a domain are cTⁿ
-- statement:
--   Let $R$ be a commutative ring that is an integral domain, and let $f$ be an element of the ring $R[T;T^{-1}]$ of Laurent polynomials over $R$ (Mathlib's `LaurentPolynomial`, the monoid algebra of $\mathbb{Z}$ over $R$). The assertion is an equivalence: $f$ is a unit of $R[T;T^{-1}]$ if and only if there exist a unit $c$ of $R$ and an integer $n$ such that $f = C(c) \cdot T^{n}$, where $C$ is the inclusion of $R$ as constant Laurent polynomials and $T^{n}$ denotes the monomial attached to $n \in \mathbb{Z}$. Thus the unit group of a Laurent polynomial ring over a domain consists exactly of the monomials with invertible coefficient; the existential is stated with $c$ ranging over $R^{\times}$ rather than over $R$ together with an invertibility hypothesis.
--
--   This is the standard description of the units of a Laurent polynomial ring over an integral domain. It is used in the classification of invertible glued data on two charts, namely by [`TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible) and its semilinear counterpart [`TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible`](thm.html#TwoChartCech.exists_semilinearEquiv_gluedLinesSections_of_invertible), where a unit of the Laurent ring governing the gluing must be reduced to a monomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LaurentPolynomial_isUnit_iff_exists_C_mul_T.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LaurentPolynomial

universe u

theorem LaurentPolynomial.isUnit_iff_exists_C_mul_T
    {R : Type u} [CommRing R] [IsDomain R] (f : R[T;T⁻¹]) :
    IsUnit f ↔ ∃ (c : Rˣ) (n : ℤ), f = C (c : R) * T n := by sorry
