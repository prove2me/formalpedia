-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_base_logarithmic_interpolation_numerics
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_base_logarithmic_interpolation_numerics
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:43:33.331425+00:00
-- url     : https://prove2.me/theorems/9a6c8139-145c-413e-834d-97968fd023c1
-- title:
--   Fixed data provide admissible rational logarithmic weights
-- statement:
--   For every FixedData instance, the logarithmic column and row weights have rational representatives that satisfy all the required numerical inequalities.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_base_logarithmic_interpolation_numerics
    {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    exists w v : Fin (d.m + 1) -> Rat,
      (forall i, (w i : Real) =
        OAI.PiExponent.InterpolationMatrix.columnWeights d.w0
          (OAI.PiExponent.MatrixArithmetic.logWeights
            (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i) /\
      (forall i, (v i : Real) =
        OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
          (OAI.PiExponent.MatrixArithmetic.logWeights
            (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i) /\
      OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics
        d.m d.K w v d.sigma := by sorry
