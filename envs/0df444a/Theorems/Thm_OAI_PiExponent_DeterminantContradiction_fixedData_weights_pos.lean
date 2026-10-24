-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_weights_pos
-- name    : OAI.PiExponent.DeterminantContradiction.fixedData_weights_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:13:32.713294+00:00
-- url     : https://prove2.me/theorems/a6cc513f-09db-44de-b456-a8222e860805
-- title:
--   Fixed determinant data has positive column weights
-- statement:
--   The base column weight and every logarithmic denominator weight of admissible fixed data are positive.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.DeterminantContradiction.fixedData_weights_pos
    (nu : Real) (d : FixedData nu) :
    0 < (d.w0 : Real) ∧
      ∀ i : Fin d.m,
        0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by sorry
