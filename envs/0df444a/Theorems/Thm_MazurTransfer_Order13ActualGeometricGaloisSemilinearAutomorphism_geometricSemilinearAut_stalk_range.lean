-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphism_geometricSemilinearAut_stalk_range
-- name    : MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_stalk_range
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:24:29.978744+00:00
-- url     : https://prove2.me/theorems/6625933c-8e88-461b-a149-a1c4e63ec80f
-- title:
--   Actual Galois semilinear lift transports every stalk range
-- statement:
--   The original actual semilinear Galois function-field lift sends the stalk range at the Galois image of each literal curve point to the stalk range at that point. The complete original characteristic-zero algebraically closed field telescope and original constructors are retained.
-- source:
--   MazurTheorem MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_stalk_range; complete original statement and checked original curve/function-field constructors, using official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2 where applicable, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_stalk_range (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (x : curveScheme K) :
    (SemilinearAut.toRingAut (geometricSemilinearAut K σ)) ''
        ((algebraMap ((curveScheme K).presheaf.stalk ((geometricCurveGaloisIso K σ).hom.base x))
          (actualCurveFunctionField K)).range : Set (actualCurveFunctionField K)) =
      ((algebraMap ((curveScheme K).presheaf.stalk x) (actualCurveFunctionField K)).range :
        Set (actualCurveFunctionField K)) := by sorry
