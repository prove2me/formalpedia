-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_actualMatrix_mulVec_eq_truncatedJetCoeff
-- name    : OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:35:46.227325+00:00
-- url     : https://prove2.me/theorems/41ad03fb-e224-4cbd-9e92-f864df11005d
-- title:
--   The concrete matrix computes truncated jet coefficients
-- statement:
--   For an admissible determinant family and a weighted polynomial, the concrete truncated logarithmic matrix applied to the polynomial coefficient vector equals the coefficient packet of the truncated logarithmic jet at every row.
-- source:
--   openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a, OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean, theorem truncatedLogMatrix_mulVec_eq_coeff

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff
    {nu : Real} (d : FixedData nu) (H : Rat)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) (H : Real)) :
    forall rho : Row d H,
      (actualMatrix d (H : Real)).mulVecLin
          (fun c : Column d (H : Real) =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
                MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d) i) + MvPowerSeries.X i.succ +
              FormalInterpolation.liftSeries d.m
                ((PowerSeries.trunc
                  (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                  (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val) := by sorry
