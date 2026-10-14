-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_product_coefficient_allocation
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_product_coefficient_allocation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:23:32.802261+00:00
-- url     : https://prove2.me/theorems/adff1822-0307-4b39-abbb-9bd1d50ce0e2
-- title:
--   Nonzero coefficients of finite multivariate polynomial products admit exponent allocations
-- statement:
--   For a finite family of multivariate polynomials over a commutative semiring, a nonzero coefficient of their product at exponent vector e implies that one can select a nonzero coefficient exponent from each factor so that the selected exponents sum to e.

import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_product_coefficient_allocation
    {ι σ R : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [CommSemiring R] (P : ι → MvPolynomial σ R) (e : σ →₀ Nat)
    (h : MvPolynomial.coeff e (∏ i, P i) ≠ 0) :
    ∃ d : ι → σ →₀ Nat,
      (∀ i, MvPolynomial.coeff (d i) (P i) ≠ 0) ∧
      (∑ i, d i = e) := by sorry
