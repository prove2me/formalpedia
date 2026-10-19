-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisLineBundle_actualGeometricPointLineBundle_galois_iso_pullback
-- name    : MazurTransfer.Order13ActualPicardGeometricGaloisLineBundle.actualGeometricPointLineBundle_galois_iso_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:40:12.153718+00:00
-- url     : https://prove2.me/theorems/135a547e-4044-41a0-8149-715a79df4b22
-- title:
--   Actual geometric Picard Galois line-bundle pullback compatibility
-- statement:
--   The existing precomposition Galois action on the actual rational Picard scheme pulls its actual geometric line bundle back along the literal curve Galois isomorphism, over every perfect characteristic-zero field, with the complete original telescope retained.
-- source:
--   MazurTheorem Order13ActualPicardGeometricGaloisLineBundle.actualGeometricPointLineBundle_galois_iso_pullback; exact original actual Picard point and line-bundle constructors.

import Definitions.Def_MazurTransfer_Order13ActualGeometricCurveGaloisAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricDiamondLineBundle Order13GeometricRelativeCurveChange
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualNormKernelProductCardinality
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018

theorem MazurTransfer.Order13ActualPicardGeometricGaloisLineBundle.actualGeometricPointLineBundle_galois_iso_pullback (K : Type) [Field K] [CharZero K] [PerfectField K]
    (σ : K ≃ₐ[ℚ] K) (a : Points K) :
    Nonempty (actualGeometricPointLineBundle K (pointOfOverHom K (actionHom K σ a)) ≅
      (Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj
        (actualGeometricPointLineBundle K (pointOfOverHom K a))) := by sorry
