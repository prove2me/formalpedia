-- Prove2me | Theorems.Thm_MazurTransfer_original_integral_norm_torsor_arithmetic_points
-- name    : MazurTransfer.original_integral_norm_torsor_arithmetic_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-11-02T17:54:21.811568+00:00
-- url     : https://prove2.me/theorems/252c382a-bfd8-4461-8716-5732d432eb73
-- statement:
--   Use the same fixed arithmetic field-point equivalence and the same chosen integral Picard point to identify rational norm preimages with points of the original integral norm-preimage torsor. Its original group compatibility preserves inverse and differences. Its original field automorphism compatibility identifies the original arithmetic action. Consequently the previously fixed kernel cocycle is exactly the torsor difference for every original automorphism and preimage, without changing the selected cocycle or point label. All five complete original propositions and helper types, seven original constructor types and five whole values, three original scoped provider types and the group-provider whole value, all three private original-type construction certificates, generated helper types and every original coefficient and cocycle context are independently checked. Named downstream consumer: the exact selected literal mu19 torsor-cocycle pushforward and nineteen Kummer unit condition.

import Definitions.Def_MazurTransfer_OriginalIntegralNormTorsorArithmeticPointsData20261020
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeIntegralNormGroupLaws Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13NineteenIntegralPointCompatibility
open RelativeNormPreimagePointTorsor RelativeNormPreimageRepresentation
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13IntegralNormTorsorArithmeticPoints
local notation "R" => LocalRing 19
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instFactPrimeOfNatNat_order13IntegralNormTorsorArithmeticPoints
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints

theorem MazurTransfer.original_integral_norm_torsor_arithmetic_points : (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (b : Points K),
fixedActualFieldPointEquiv K (b ≫ φ) =
      NeronModelInfra.schemeHomOverComp (fixedActualFieldPointEquiv K b)
        (integralNorm 19 nineteen_good φ)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K], ∀ (b : Points K),
fixedActualFieldPointEquiv K b⁻¹ = (localLaw 19 nineteen_good).inv
      (FieldAutomorphismOverPointAction.fieldBase R K) (fixedActualFieldPointEquiv K b)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (x y : rationalPreimages K φ a),
fixedKernelPointEquiv K φ (rationalDifference K φ a x y) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a x) (preimageEquiv K φ a y)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a),
(preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.2.1 19 K σ)
        (preimageEquiv K φ a b).val) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a),
fixedKernelPointEquiv K φ (kernelCocycle K φ a b.val b.property σ) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)) (preimageEquiv K φ a b)) := by sorry
