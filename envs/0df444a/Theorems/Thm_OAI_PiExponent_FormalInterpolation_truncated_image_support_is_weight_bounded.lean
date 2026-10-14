-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_image_support_is_weight_bounded
-- name    : OAI.PiExponent.FormalInterpolation.truncated_image_support_is_weight_bounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T08:48:09.947837+00:00
-- url     : https://prove2.me/theorems/79b13806-def2-41a5-8a14-321ffeaa120b
-- title:
--   Column support satisfies the weighted bound
-- statement:
--   Any polynomial supported on exponents of bounded columns satisfies the weighted degree bound on every support exponent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_image_support_is_weight_bounded
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P.support ⊆ Finset.univ.image
      (fun c : InterpolationMatrix.Column w0 w H =>
        InterpolationMatrix.exponentVector c.1)) :
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H := by sorry
