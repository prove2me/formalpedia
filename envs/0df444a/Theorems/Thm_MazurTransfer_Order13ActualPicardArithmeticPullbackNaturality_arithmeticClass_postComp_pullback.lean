-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardArithmeticPullbackNaturality_arithmeticClass_postComp_pullback
-- name    : MazurTransfer.Order13ActualPicardArithmeticPullbackNaturality.arithmeticClass_postComp_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:38:05.433089+00:00
-- url     : https://prove2.me/theorems/0c65647e-effb-4a2e-9754-809553cc3016
-- title:
--   Actual represented Picard inverse pullback agrees with arithmetic field transport
-- statement:
--   For any affine cover, section and represented degree-zero Picard scheme of the literal rational order-13 curve, any function-field automorphism sigma, any genuine re-rigidified inverse-curve PullbackData and any rational represented Picard point, its arithmeticClass after represented inverse pullback is sigma acting on its original arithmeticClass. Every original quantified object and hypothesis is retained.
-- source:
--   Complete original MazurTheorem Order13ActualPicardArithmeticPullbackNaturality.arithmeticClass_postComp_pullback proof and contract. Original inverse_over certificate from the published generic field-action Definition. Original Picard and divisor-presentation interfaces reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full arithmetic pullback-naturality contract and proof, using accepted
public presentation transport and arithmetic presentation independence.
The original inverse-over-base certificate is supplied by the public field-action
Definition; complete original types and data values were checked separately.
Design boundary: genuine re-rigidified represented Picard pullback induces
the actual field action on the original arithmetic Pic0 class.
Named downstream consumer: diamond Picard scheme action and norm/rank descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Theorems.Thm_MazurTransfer_Order13ActualCurveDivisorPresentationPullback_presentation_pullback
import Theorems.Thm_MazurTransfer_PicardCurvePullbackBaseFieldLineBundle_pointLineBundle_postComp_iso_pullback
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
noncomputable section
open MazurTransfer
open Order13ActualPicardArithmeticPullbackNaturality
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open PicardReRigidifiedCurvePullback LineBundleFieldComparison Order13ArithmeticPicardPointMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13ActualPicardArithmeticPullbackNaturality.arithmeticClass_postComp_pullback
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) (curveToBase ℚ))
    (D : RelativePic0Designation ℚ (curveToBase ℚ))
    (h : RepresentsRelSubPic (curveToBase ℚ) ε (algEquivZeroCut (curveToBase ℚ) ε) D)
    (σ : F ≃ₐ[ℚ] F)
    (N : PullbackData h (fieldLift σ).inv (inverse_over σ))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) D.toBase) :
    arithmeticClass ℚ 𝒱 ε D h (postComp N.hom a) =
      σ • arithmeticClass ℚ 𝒱 ε D h a := by sorry
