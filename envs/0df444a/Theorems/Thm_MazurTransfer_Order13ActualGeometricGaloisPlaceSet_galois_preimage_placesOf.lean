-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisPlaceSet_galois_preimage_placesOf
-- name    : MazurTransfer.Order13ActualGeometricGaloisPlaceSet.galois_preimage_placesOf
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:26:55.467055+00:00
-- url     : https://prove2.me/theorems/a7778106-cb8e-4862-8d01-a28ffbad2520
-- title:
--   Actual Galois preimages transport literal sets of closed-point places
-- statement:
--   For every open of the literal actual curve, its Galois preimage has exactly the places obtained by applying the original actual semilinear Galois lift. The complete original characteristic-zero algebraically closed field telescope and original constructors are retained.
-- source:
--   MazurTheorem MazurTransfer.Order13ActualGeometricGaloisPlaceSet.galois_preimage_placesOf; complete original statement and checked original curve/function-field constructors, using official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2 where applicable, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13FieldCurveInversePlaceSetData
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGeometricGaloisPlaceSet.galois_preimage_placesOf (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (U : (curveScheme K).Opens) :
    placesOf (curveToBase K) ((geometricCurveGaloisIso K σ).hom ⁻¹ᵁ U) =
      (fun v : Place K (actualCurveFunctionField K) => geometricSemilinearAut K σ • v) ''
        placesOf (curveToBase K) U := by sorry
