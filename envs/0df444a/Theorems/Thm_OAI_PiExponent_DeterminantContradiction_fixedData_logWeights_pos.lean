-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_logWeights_pos
-- name    : OAI.PiExponent.DeterminantContradiction.fixedData_logWeights_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:44:41.247858+00:00
-- url     : https://prove2.me/theorems/fbf6a26b-0124-463f-9c9d-b1c54f79337d
-- title:
--   Positivity of fixed-data logarithmic weights
-- statement:
--   Every logarithmic denominator weight of fixed admissible data is positive: each denominator is at least 2, so its logarithm and its natural-number ceiling are positive.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.fixedData_logWeights_pos (nu : Real) (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by sorry
