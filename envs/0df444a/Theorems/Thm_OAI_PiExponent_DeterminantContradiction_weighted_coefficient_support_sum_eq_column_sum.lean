-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_coefficient_support_sum_eq_column_sum
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_coefficient_support_sum_eq_column_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:19:42.577293+00:00
-- url     : https://prove2.me/theorems/1b5dbfc1-52cd-401e-aab6-c023e66d6279
-- title:
--   Reindex a coefficient-weighted support sum by columns
-- statement:
--   Reindex the sum of a function times polynomial coefficients from the supported exponents to the interpolation columns. The weighted support hypothesis places each supported exponent in the inclusive column simplex, while coefficients vanish for exponents outside the support.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.weighted_coefficient_support_sum_eq_column_sum
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (f : (Fin (d.m + 1) →₀ Nat) → Complex) :
    (∑ a ∈ P.1.support, f a * P.1.coeff a) =
      ∑ c : Column d H,
        f (InterpolationMatrix.exponentVector c.1) *
          P.1.coeff (InterpolationMatrix.exponentVector c.1) := by sorry
