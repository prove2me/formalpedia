-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_polynomial_coefficient_interpolation
-- name    : OAI.PiExponent.FormalInterpolation.finite_polynomial_coefficient_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-08T06:29:43.450481+00:00
-- url     : https://prove2.me/theorems/a84d3a7d-1b2f-4849-ae5c-a67b725395e8
-- title:
--   Finite coefficient interpolation by a polynomial
-- statement:
--   For a finite set of exponent vectors, every assignment of complex coefficients is realized by the corresponding coefficients of an ordinary polynomial, viewed as a multivariate formal power series. The witness is a finite sum of the assigned values times their monomials.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent

theorem OAI.PiExponent.FormalInterpolation.finite_polynomial_coefficient_interpolation
    {m : ℕ} (S : Finset (Fin (m + 1) → ℕ)) :
    ∀ y : ↥ S → ℂ, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ a : ↥ S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (Q : MvPowerSeries (Fin (m + 1)) ℂ) = y a := by sorry
