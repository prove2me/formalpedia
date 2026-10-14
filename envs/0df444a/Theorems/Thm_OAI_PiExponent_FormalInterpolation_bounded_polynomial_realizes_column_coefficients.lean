-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_polynomial_realizes_column_coefficients
-- name    : OAI.PiExponent.FormalInterpolation.bounded_polynomial_realizes_column_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T05:34:46.153982+00:00
-- url     : https://prove2.me/theorems/abe97f0d-8139-4635-af95-c0f10659a59c
-- title:
--   A bounded weighted polynomial realizes any admissible column coefficient vector
-- statement:
--   Every complex-valued coefficient vector indexed by the admissible weighted columns is realized by a weighted polynomial whose support obeys the same bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.bounded_polynomial_realizes_column_coefficients
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (x : InterpolationMatrix.Column w0 w H → Complex) :
    ∃ Q : WeightedPolynomial w0 w H,
      ∀ c : InterpolationMatrix.Column w0 w H,
        Q.val.coeff (InterpolationMatrix.exponentVector c.1) = x c := by sorry
