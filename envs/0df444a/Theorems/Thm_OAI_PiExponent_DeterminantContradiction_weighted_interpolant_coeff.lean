-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_interpolant_coeff
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_interpolant_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:26:27.143996+00:00
-- url     : https://prove2.me/theorems/ac3312e9-a0c4-4a04-9f37-13e360e6c758
-- title:
--   Coefficient extraction recovers the indexed value
-- statement:
--   At the exponent for column c, the coefficient of the finite monomial sum is exactly f c; distinct columns have distinct exponent vectors.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.DeterminantContradiction.weighted_interpolant_coeff (nu : Real) (d : FixedData nu) (H : Real) (f : Column d H → Complex) (c : Column d H) : (∑ c' : Column d H, MvPolynomial.C (f c') * MvPolynomial.monomial (InterpolationMatrix.exponentVector c'.1) 1).coeff (InterpolationMatrix.exponentVector c.1) = f c := by sorry
