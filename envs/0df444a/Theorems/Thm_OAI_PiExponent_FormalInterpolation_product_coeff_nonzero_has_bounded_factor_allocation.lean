-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_product_coeff_nonzero_has_bounded_factor_allocation
-- name    : OAI.PiExponent.FormalInterpolation.product_coeff_nonzero_has_bounded_factor_allocation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:19:11.67915+00:00
-- url     : https://prove2.me/theorems/45d9586a-bdcc-48f2-a339-667c830255b4
-- title:
--   Nonzero product coefficients admit bounded exponent allocations
-- statement:
--   If the target coefficient in a finite product of multivariate polynomials is nonzero, then there is a choice of one exponent for each factor such that each chosen exponent is bounded coordinatewise by the target, the chosen exponents sum coordinatewise to the target, and each corresponding factor coefficient is nonzero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.product_coeff_nonzero_has_bounded_factor_allocation
    {m n : Nat} (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hprod : MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) ≠ 0) :
    ∃ b : Fin n → Fin (m + 1) → Nat,
      (∀ i, b i ≤ a) ∧
      (∀ j, (∑ i, b i j) = a j) ∧
      (∀ i, MvPolynomial.coeff (InterpolationMatrix.exponentVector (b i)) (F i) ≠ 0) := by sorry
