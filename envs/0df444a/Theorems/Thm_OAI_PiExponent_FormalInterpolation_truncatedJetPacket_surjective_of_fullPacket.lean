-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedJetPacket_surjective_of_fullPacket
-- name    : OAI.PiExponent.FormalInterpolation.truncatedJetPacket_surjective_of_fullPacket
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T06:35:55.733626+00:00
-- url     : https://prove2.me/theorems/d0d1afad-8cdf-4969-ad45-60f9f32d35e6
-- title:
--   Transfer packet surjectivity through logarithmic truncation
-- statement:
--   For admissible determinant data, if the cutoff orders dominate the weighted row coordinates and the full formal logarithmic packet map is surjective, then the coefficient packets formed with the truncated logarithms are also surjective. The cutoff condition ensures the logarithmic tails lie in the weighted ideal, so the invertible formal variable shift preserves packets modulo that ideal.
-- source:
--   openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a, OAI/NumberTheory/PiExponent/Analysis/FormalLogTruncation.lean, theorem formalLog_packets_surjective_iff_truncated

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.truncatedJetPacket_surjective_of_fullPacket
    {nu : Real} (d : FixedData nu) (H : Rat)
    (hT : forall i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : Real) <=
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : Real) *
          (d.v0 : Real))
    (hpacket : Function.Surjective
      (FormalInterpolation.packetMap d (H : Real))) :
    Function.Surjective
      (fun P : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) (H : Real) =>
        fun rho : Row d H =>
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
            (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
              (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
                  MatrixArithmetic.rationalCenters (finiteNumerators d)
                    (finiteDenominators d) i) + MvPowerSeries.X i.succ +
                FormalInterpolation.liftSeries d.m
                  ((PowerSeries.trunc
                    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                    (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val)) := by sorry
