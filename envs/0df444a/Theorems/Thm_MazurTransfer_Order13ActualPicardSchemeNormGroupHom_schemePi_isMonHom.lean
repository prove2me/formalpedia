-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
-- name    : MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:53:41.855908+00:00
-- url     : https://prove2.me/theorems/cbbacf6a-de6e-44f3-b9b0-30abbc610939
-- title:
--   The actual rational Picard norm factor pi is an internal group morphism
-- statement:
--   Let P be the same actual rational represented Picard scheme, with its original internal commutative group structure. The existing norm factor pi is an internal group morphism of P over Q. For pi and pi-bar, these are the original endomorphisms 3 id+2 delta and 5 id-2 delta, using the Picard group law. The named downstream consumers are the actual norm isogenies and their scheme kernels.
-- source:
--   Complete original MazurTheorem Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom, retaining the original full type, original helper arguments and original group-object and scalar providers. Uses the existing accepted public monoid Yoneda criterion and the same actual represented Picard and pullback action. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual Picard diamond and both nineteen-norm
endomorphisms are internal group morphisms, by preservation on all test
schemes. Named downstream consumer: scheme isogenies and descent kernels.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_MonoidObjectMorphismFromPointwiseGroupLaw_isMonHom_of_all_points

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance publicStatementactualPicardPiGroupMorphismProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj



local instance publicStatementactualPicardPiGroupMorphismProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicStatementactualPicardPiGroupMorphismProvider320261017 : Algebra ℚ (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ
local instance publicStatementactualPicardPiGroupMorphismProvider420261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj

theorem MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom : IsMonHom schemePi := by sorry
