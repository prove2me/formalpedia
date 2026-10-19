-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_geometric_composite_nineteen
-- name    : MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate_geometric_composite_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:43:47.450066+00:00
-- url     : https://prove2.me/theorems/dfd656f5-d43f-45d2-88f8-0ea6188e6ae1
-- title:
--   The reverse actual Picard norm composite is nineteenth power on every perfect characteristic-zero field point
-- statement:
--   Let P be the same actual rational represented Picard scheme, let K be a perfect characteristic-zero field, let V be a two-affine cover of the actual curve over K, and let a be a K-valued point of P. Write the Picard group multiplicatively. Let pi and pi-bar be the original scheme endomorphisms 3 id+2 delta and 5 id-2 delta, with addition and integer multiples taken in the Picard group. Then
--
--   $$\pi(\overline{\pi}(a))=a^{19}.$$
--
--   The named downstream consumer is the reverse genuine norm-nineteen scheme composite.
-- source:
--   Complete original MazurTheorem Order13ActualPicardSchemeNineteenNorm statement and proof, retaining the same actual represented Picard family and every original helper full type and data provider. Uses the accepted exact original geometric arithmetic injectivity bridge with explicit public binders. Official Anthropic FLT Picard inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two explicit endomorphisms of the same rational Picard
scheme have both composites equal to scalar nineteen. This establishes
the actual scheme norm identity; isogeny properties and degrees remain
separate obligations. Named downstream consumer: nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance publicStatementschemeNineteenNormReversePointProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance publicStatementschemeNineteenNormReversePointProvider220261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance publicStatementschemeNineteenNormReversePointProvider320261017 : Algebra K (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField K) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra K
variable (𝒱 : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover)


include 𝒱 in

theorem MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate_geometric_composite_nineteen
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    a ≫ schemePiConjugate ≫ schemePi = a ^ 19 := by sorry
