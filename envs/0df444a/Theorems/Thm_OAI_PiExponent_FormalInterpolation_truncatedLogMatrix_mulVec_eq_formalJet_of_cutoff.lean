-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff
-- name    : OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-07T20:32:47.758353+00:00
-- url     : https://prove2.me/theorems/b459a77f-8e02-405b-b67a-a5ea1ecc1b83
-- title:
--   Cutoff stability for weighted logarithmic interpolation
-- statement:
--   For arbitrary interpolation parameters with positive row weights, the truncated logarithmic interpolation matrix applied to the coefficients of a weighted polynomial equals the corresponding coefficient of the full formal logarithmic jet. The cutoff hypothesis says each truncated logarithm starts beyond the weight budget assigned to its variable, so its omitted tail cannot affect any row packet below the polynomial weighted height.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixBridge.lean (generalized coefficient identity; cutoff argument from Analysis/FormalLogTruncation.lean)

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.truncatedLogMatrix_mulVec_eq_formalJet_of_cutoff
    {m K : Nat} (w0 v0 theta H : Real) (w : Fin m -> Real)
    (T : Fin m -> Nat) (r : Fin m -> Complex)
    (P : FormalInterpolation.WeightedPolynomial w0 w H)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : forall i, 0 <= w i)
    (hT : forall i, w i / theta <= (T i : Real) * v0) :
    forall rho : InterpolationMatrix.Row K v0 theta w H,
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c : InterpolationMatrix.Column w0 w H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (FormalInterpolation.formalJet
            (fun i => (rho.1.val : Complex) * r i) P.val) := by sorry
