-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_sum_eq_column_sum
-- name    : OAI.PiExponent.FormalInterpolation.support_sum_eq_column_sum
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:57:22.026153+00:00
-- url     : https://prove2.me/theorems/372dfa28-f191-439b-90c9-18e17cb1e8cf
-- title:
--   Reindex a polynomial support sum by interpolation columns
-- statement:
--   If every exponent in a polynomial's support is represented by an interpolation column, then summing a function of supported exponents with the polynomial coefficients is equal to summing the same function over all interpolation columns; columns outside the support contribute zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.support_sum_eq_column_sum
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (F : (Fin (m + 1) →₀ Nat) → Complex)
    (hcols : ∀ e ∈ P.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = e) :
      ∑ e ∈ P.support, P.coeff e * F e =
        ∑ c : InterpolationMatrix.Column w0 w H,
          P.coeff (InterpolationMatrix.exponentVector c.1) *
            F (InterpolationMatrix.exponentVector c.1) := by sorry
