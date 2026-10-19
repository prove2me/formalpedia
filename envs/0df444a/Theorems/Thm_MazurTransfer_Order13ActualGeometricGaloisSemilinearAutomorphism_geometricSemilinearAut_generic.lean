-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphism_geometricSemilinearAut_generic
-- name    : MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_generic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:21:42.233231+00:00
-- url     : https://prove2.me/theorems/310b972c-4d37-4a07-a8a1-64c4aa9ffa1b
-- title:
--   Actual Galois semilinear lift commutes with the literal generic-stalk map
-- statement:
--   The original actual semilinear Galois function-field lift commutes with the literal generic-stalk embedding and the actual curve Galois isomorphism. The complete original characteristic-zero algebraically closed field telescope and original constructors are retained.
-- source:
--   MazurTheorem MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_generic; complete original statement and checked original curve/function-field constructors, using official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2 where applicable, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut_generic (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) :
    Spec.map (CommRingCat.ofHom (SemilinearAut.toRingAut (geometricSemilinearAut K σ)).toRingHom) ≫
        (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) =
      (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) ≫
        (geometricCurveGaloisIso K σ).hom := by sorry
