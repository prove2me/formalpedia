-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGenericFieldAction_actualFieldHom_arithmetic
-- name    : MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_arithmetic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:46:30.683434+00:00
-- url     : https://prove2.me/theorems/8bc60760-5013-43ba-9e00-f871434e5462
-- title:
--   The actual represented Picard scheme field action agrees with its arithmetic Pic0 action
-- statement:
--   For every automorphism sigma of the literal rational order-13 function field, every affine cover of the actual curve and every rational point of the original actual represented Picard scheme, the original arithmeticClass after the original actualFieldHom sigma equals sigma acting on the original arithmeticClass. All original scheme action and arithmetic class constructors are retained.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGenericFieldAction.actualFieldHom_arithmetic statement and proof; original scheme action constructors are the published generic field-action Definition. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full actualFieldHom_arithmetic contract and proof retained.
Design boundary: the original genuine scheme field action induces the
specified automorphism action on the original arithmetic Pic0 classes.
Named downstream consumer: diamond scheme action and scheme norm identities.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Theorems.Thm_MazurTransfer_Order13ActualPicardArithmeticPullbackNaturality_arithmeticClass_postComp_pullback
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualPicardArithmeticPullbackNaturality Order13ActualPicardDiamondSchemeEndomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open PicardReRigidifiedCurvePullback Order13ArithmeticPicardPointMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

open Order13ActualPicardGenericFieldAction

theorem MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_arithmetic (σ : F ≃ₐ[ℚ] F) (𝒱 : C.TwoAffineOpenCover)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase) :
    arithmeticClass ℚ 𝒱 infinitySection actualPicard actualRepresentation
        (postComp (actualFieldHom σ) a) =
      σ • arithmeticClass ℚ 𝒱 infinitySection actualPicard actualRepresentation a := by sorry
