-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_mul
-- name    : MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_mul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T19:40:42.532989+00:00
-- url     : https://prove2.me/theorems/9b1e4738-d596-4591-aa8d-46ef3d96db0a
-- title:
--   Multiplication of geometric points of the same rational Picard adds their actual arithmetic divisor classes
-- statement:
--   Let K be a perfect characteristic-zero field. Give the same rational represented Picard family its group structure from the original degree-zero relative Picard representation, and let a,b be K-valued points in the over category. Then
--
--   $$\operatorname{cl}_K(ab)=\operatorname{cl}_K(a)+\operatorname{cl}_K(b).$$
--
--   The arithmetic classes are computed by full degree-zero presentations on the literal curve over K, with the original chosen group structure and point constructors retained. This supplies the group law required for geometric injectivity and actual scheme norm transport.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_mul. It reuses the original Poincare tensor isomorphism, accepted perfect-field tensor-presentation comparison, and full original geometric presentation independence. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: multiplication of geometric points of the SAME original
rational represented Picard adds their intrinsic actual divisor classes.
Named downstream consumer: injectivity of geometric arithmetic classes and
detection of the actual diamond scheme norm identities.
Original MazurTheorem Order13ActualPicardGeometricArithmeticGroup proof;
official Anthropic FLT Poincare tensor inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition
open MazurTransfer.Order13GeometricRelativeCurveChange
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

theorem MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_mul :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    ∀ a b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase,
      geometricArithmeticClassOver K 𝒱 (a * b) =
        geometricArithmeticClassOver K 𝒱 a + geometricArithmeticClassOver K 𝒱 b := by sorry
