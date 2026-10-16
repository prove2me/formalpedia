-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
-- name    : OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:47:00.506249+00:00
-- url     : https://prove2.me/theorems/9e154cda-97cb-46d4-a9dd-403bc05e0c12
-- title:
--   Positive weighted support exponents lie in the interpolation columns
-- statement:
--   Every exponent in the support of a polynomial with positive column weights and weighted support bound is represented by a column in the interpolation simplex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights_weighted_support_columns
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : WeightedPolynomial w0 w H) :
    ∀ a ∈ P.val.support,
      ∃ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.exponentVector c.1 = a := by sorry
