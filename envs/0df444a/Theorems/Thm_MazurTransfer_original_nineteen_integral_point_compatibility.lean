-- Prove2me | Theorems.Thm_MazurTransfer_original_nineteen_integral_point_compatibility
-- name    : MazurTransfer.original_nineteen_integral_point_compatibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-11-02T17:30:58.263627+00:00
-- url     : https://prove2.me/theorems/681192e8-5457-4922-9ff2-ad03d82437fa
-- statement:
--   Retain the original chosen unique integral extension of the same rational Picard point. Its original uniqueness and restriction properties imply the original generic projection equality. Compatibility of field base maps then identifies its field points with the previously fixed arithmetic field-point comparison over every original characteristic-zero field and scalar tower. All four complete original propositions and helper types, both original constructor full types and whole values, both scoped provider types and the group-provider whole value, the original-type private unique-extension certificate, all generated helper types and all original coefficient and arithmetic point contexts are independently checked. Named downstream consumer: both actual norm-preimage torsors and the original selected character Kummer cocycle.

import Definitions.Def_MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
import Theorems.Thm_MazurTransfer_original_exceptional_nineteen_norm_model_properties
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ExceptionalNineteenFlatNormFibres Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalGenericPicardComparison
open Order13IntegralGenericPointComparison Order13IntegralArithmeticFieldPointComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open RelativeNormPreimageRepresentation Order13ActualIntegralNormPreimageTorsors
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13NineteenIntegralPointCompatibility
local notation "R" => LocalRing 19
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instFactPrimeOfNatNat_order13NineteenIntegralPointCompatibility
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13NineteenIntegralPointCompatibility

theorem MazurTransfer.original_nineteen_integral_point_compatibility : (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) (integralPoint a) =
      actualGenericPoint a) ∧ (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), ∀ (b : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) integralModel.toBase)
    (hb : genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) b =
      actualGenericPoint a),
b = integralPoint a) ∧ (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), localGenericInclusion 19 ≫ (integralPoint a).val =
      (a.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
        pullback.fst integralModel.toBase (localGenericInclusion 19)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K], ∀ (b : RationalPoints),
fixedActualFieldPointEquiv K (rationalPoint K b) =
      pulledPoint (integralPoint (overHomToSchemeHomOver b))
        (FieldAutomorphismOverPointAction.fieldBase R K)) := by sorry
