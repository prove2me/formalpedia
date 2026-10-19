-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_kernel_killed_nineteen
-- name    : MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_kernel_killed_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:52:15.940109+00:00
-- url     : https://prove2.me/theorems/f51148e2-87f5-4348-892f-33d07c82cb67
-- title:
--   The actual pi-bar norm kernel is killed by nineteen on every test scheme
-- statement:
--   Let P be the same actual rational represented Picard group scheme and let pi-bar be its original norm endomorphism. For every scheme T over Q and every T-valued point a of P in the kernel of this norm map, multiplication by nineteen kills a. This holds functorially on all test schemes. The named downstream consumers are the original norm Kummer cocycles and the finite Galois kernel modules.
-- source:
--   Complete original MazurTheorem Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_kernel_killed_nineteen statement and main proof body. Same actual Picard, original norm constructors and group provider; final original full type and original scalar/group provider values independently compared. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual Picard diamond and both nineteen-norm
endomorphisms are internal group morphisms, by preservation on all test
schemes. Named downstream consumer: scheme isogenies and descent kernels.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData


noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance publicStatementActualPiConjugateKernelKilledNineteenProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj



local instance publicStatementActualPiConjugateKernelKilledNineteenProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicStatementActualPiConjugateKernelKilledNineteenProvider320261017 : Algebra ℚ (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ
local instance publicStatementActualPiConjugateKernelKilledNineteenProvider420261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj

theorem MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_kernel_killed_nineteen (T : Over (Spec (CommRingCat.of ℚ)))
    (a : T ⟶ Over.mk actualPicard.toBase) (ha : a ≫ schemePiConjugate = 1) : a ^ 19 = 1 := by sorry
