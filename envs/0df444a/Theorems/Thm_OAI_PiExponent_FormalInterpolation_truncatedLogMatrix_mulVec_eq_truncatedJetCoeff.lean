-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedLogMatrix_mulVec_eq_truncatedJetCoeff
-- name    : OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_truncatedJetCoeff
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-08T17:11:34.2173+00:00
-- url     : https://prove2.me/theorems/55056d74-2dc6-497b-85ff-503762716411
-- title:
--   Coefficient identity for the truncated-log interpolation matrix
-- statement:
--   For arbitrary interpolation parameters, multiplying the truncated-log interpolation matrix by the vector of polynomial coefficients gives the coefficient of the matching truncated formal logarithmic jet. The row and column indices range over the weighted simplices defined for the interpolation matrix.
-- source:
--   OpenAI Math, FormalMatrixBridge.linearEvaluation_eq_coeff, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
set_option maxHeartbeats 1000000

theorem OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_truncatedJetCoeff
    {m : Nat} (K : Nat) (w0 v0 theta H : Real) (w : Fin m -> Real)
    (T : Fin m -> Nat) (r : Fin m -> Complex)
    (P : FormalInterpolation.WeightedPolynomial w0 w H) :
    forall rho : InterpolationMatrix.Row K v0 theta w H,
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
          (fun c : InterpolationMatrix.Column w0 w H =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C ((rho.1.val : Complex) * r i) +
              MvPowerSeries.X i.succ +
              FormalInterpolation.liftSeries m
                ((PowerSeries.trunc (T i) (PowerSeries.log Complex) : Polynomial Complex) :
                  PowerSeries Complex))) P.val) := by sorry
