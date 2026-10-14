-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_column_exponent_support_is_bounded
-- name    : OAI.PiExponent.FormalInterpolation.column_exponent_support_is_bounded
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T05:38:38.636463+00:00
-- url     : https://prove2.me/theorems/1b3eb9b9-e077-4522-bdb2-e9b38477f269
-- title:
--   Support on admissible column exponents satisfies the weighted bound
-- statement:
--   If a polynomial's support is contained in the exponents of admissible columns, then every exponent in its support satisfies the weighted degree bound defining `WeightedPolynomial`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.column_exponent_support_is_bounded
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P.support ⊆ Finset.univ.image
      (fun c : InterpolationMatrix.Column w0 w H =>
        InterpolationMatrix.exponentVector c.1)) :
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H := by sorry
