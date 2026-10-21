-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_logarithmic_interpolation_numerics
-- name    : OAI.PiExponent.FormalInterpolation.fixedData_canonical_logarithmic_interpolation_numerics
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T08:52:58.263306+00:00
-- url     : https://prove2.me/theorems/41cb57a4-41e5-44e0-bef4-8dd07ccd67f8
-- title:
--   Canonical logarithmic weights satisfy the interpolation numerics
-- statement:
--   For every FixedData instance, the explicitly prescribed rational vectors formed from its base weights and ceiling logarithms agree with the real logarithmic column and row weights and satisfy all logarithmic interpolation numerical conditions.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fixedData_canonical_logarithmic_interpolation_numerics
    {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    let w : Fin (d.m + 1) -> Rat :=
      fun i => Fin.cases d.w0
        (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
    let v : Fin (d.m + 1) -> Rat :=
      fun i => Fin.cases d.v0
        (fun j =>
          (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
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
