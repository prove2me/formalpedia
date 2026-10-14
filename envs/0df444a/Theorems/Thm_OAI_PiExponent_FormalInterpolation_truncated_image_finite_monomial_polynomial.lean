-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_image_finite_monomial_polynomial
-- name    : OAI.PiExponent.FormalInterpolation.truncated_image_finite_monomial_polynomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:47:56.05435+00:00
-- url     : https://prove2.me/theorems/0041a687-2cb3-484e-a5f7-86aa254aa9c8
-- title:
--   Interpolate coefficients on the finite column set
-- statement:
--   Construct a multivariate polynomial that has the prescribed coefficient at every bounded column exponent and whose support contains only column exponents.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_image_finite_monomial_polynomial
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ P : MvPolynomial (Fin (m + 1)) Complex,
      (∀ c : InterpolationMatrix.Column w0 w H,
        P.coeff (InterpolationMatrix.exponentVector c.1) = x c) ∧
      P.support ⊆ Finset.univ.image
        (fun c : InterpolationMatrix.Column w0 w H =>
          InterpolationMatrix.exponentVector c.1) := by sorry
