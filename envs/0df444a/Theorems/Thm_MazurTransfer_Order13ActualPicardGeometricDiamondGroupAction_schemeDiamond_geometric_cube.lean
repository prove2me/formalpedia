-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricDiamondGroupAction_schemeDiamond_geometric_cube
-- name    : MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction.schemeDiamond_geometric_cube
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:44:53.144117+00:00
-- url     : https://prove2.me/theorems/84712f63-47af-461d-8263-c6220cde5d7f
-- title:
--   The cube of the actual rational Picard diamond inverts every perfect characteristic-zero field point
-- statement:
--   Let P be the same actual rational represented Picard scheme, let K be a perfect characteristic-zero field, let V be a two-affine cover of the actual curve over K, and let a be a K-valued point of P. Write the Picard group multiplicatively. For the existing scheme diamond delta,
--
--   $$\delta^3(a)=a^{-1}.$$
--
--   The named downstream consumer is the hyperelliptic equality of actual Picard scheme morphisms.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricDiamondGroupAction statement and proof, retaining the same actual represented Picard family and every original helper full type and data provider. Uses the accepted exact original geometric arithmetic injectivity bridge with explicit public binders. Official Anthropic FLT Picard inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational Picard diamond satisfies its
cyclotomic and hyperelliptic identities on every perfect characteristic-zero
field point, via the injective geometric divisor-class group map.
Named downstream consumer: the same identities as equalities of actual
Picard scheme morphisms, and the nineteen-norm endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017

noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open scoped CategoryTheory.MonObj
local instance publicStatementgeometricDiamondCubePointProvider120261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicStatementgeometricDiamondCubePointProvider220261017 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance publicStatementgeometricDiamondCubePointProvider320261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.GeometricDiamondGroupActionUnitHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance publicStatementgeometricDiamondCubePointProvider420261017 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance publicStatementgeometricDiamondCubePointProvider520261017 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)


include 𝒱 in

theorem MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction.schemeDiamond_geometric_cube
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase) :
    a ≫ schemeDiamond ≫ schemeDiamond ≫ schemeDiamond = a⁻¹ := by sorry
