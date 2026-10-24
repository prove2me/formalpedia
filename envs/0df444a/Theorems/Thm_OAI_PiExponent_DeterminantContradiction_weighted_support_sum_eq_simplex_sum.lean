-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_sum_eq_simplex_sum
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_simplex_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:24:09.705202+00:00
-- url     : https://prove2.me/theorems/84ed8ad0-f193-4d22-8737-61e6bf886060
-- title:
--   Expand a weighted polynomial support sum to its inclusive simplex
-- statement:
--   For a weighted polynomial, summing a function times its coefficients over the support equals summing the same terms over the full inclusive weighted simplex, with unsupported exponents contributing zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_simplex_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (f : (Fin (d.m + 1) →₀ Nat) → Complex) :
    (∑ a ∈ P.1.support, f a * P.1.coeff a) =
      ∑ a ∈ realWeightedSimplex
        (InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d))) H,
        f (InterpolationMatrix.exponentVector a) *
          P.1.coeff (InterpolationMatrix.exponentVector a) := by sorry
