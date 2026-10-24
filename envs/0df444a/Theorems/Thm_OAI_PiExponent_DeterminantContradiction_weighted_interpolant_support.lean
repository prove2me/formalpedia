-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_interpolant_support
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_interpolant_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:26:09.702093+00:00
-- url     : https://prove2.me/theorems/91d153b6-c389-4623-9aa3-13638607cff6
-- title:
--   The weighted monomial interpolant has bounded support
-- statement:
--   The finite sum of monomials indexed by columns has support only at exponents satisfying the weighted height bound.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.DeterminantContradiction.weighted_interpolant_support (nu : Real) (d : FixedData nu) (H : Real) (f : Column d H → Complex) : ∀ a ∈ (∑ c : Column d H, MvPolynomial.C (f c) * MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1).support, ∑ i, InterpolationMatrix.columnWeights d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ H := by sorry
