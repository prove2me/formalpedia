-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_column_monomial_interpolation
-- name    : OAI.PiExponent.FormalInterpolation.finite_column_monomial_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T05:38:22.732986+00:00
-- url     : https://prove2.me/theorems/ad5632e4-357d-4783-aad6-006e5ef9c626
-- title:
--   Interpolate arbitrary coefficients on a finite set of column exponents
-- statement:
--   For any complex coefficient assignment on admissible columns, there is a multivariate polynomial realizing those coefficients whose support consists only of the corresponding column exponents.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_column_monomial_interpolation
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      (∀ c : InterpolationMatrix.Column w0 w H,
        P.coeff (InterpolationMatrix.exponentVector c.1) = x c) ∧
      P.support ⊆ Finset.univ.image
        (fun c : InterpolationMatrix.Column w0 w H =>
          InterpolationMatrix.exponentVector c.1) := by sorry
