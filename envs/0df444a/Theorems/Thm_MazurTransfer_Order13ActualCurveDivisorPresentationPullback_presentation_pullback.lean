-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualCurveDivisorPresentationPullback_presentation_pullback
-- name    : MazurTransfer.Order13ActualCurveDivisorPresentationPullback.presentation_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:05:35.891979+00:00
-- url     : https://prove2.me/theorems/88519fbf-efa4-46c3-ba50-498f7dc816cb
-- title:
--   Actual rational order-13 curve: full divisor presentations under inverse pullback
-- statement:
--   For every automorphism sigma of the function field of the actual rational order-13 curve, inverse pullback of any line bundle with a full divisor presentation for D admits a full divisor presentation for sigma acting on D. The curve, generic field lift and place transport are the actual previously constructed objects.
-- source:
--   MazurTheorem, original Order13ActualCurveDivisorPresentationPullback contract and proof; presentation interfaces reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve pullback on the literal curve over Q takes
any full divisor presentation to the divisor transported by the specified
actual field automorphism. Named downstream consumer: identification of
the genuine represented Picard action with arithmetic Pic0 transport.
-/
import Theorems.Thm_MazurTransfer_CurveIsoDivisorPresentationFieldAction_presentation_pullback
import Theorems.Thm_MazurTransfer_Order13ActualCurveInversePlaceSet_inverse_placesOf
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualCurveInversePlaceSet
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13ActualCurveDivisorPresentationPullback.presentation_pullback (σ : F ≃ₐ[ℚ] F) (L : C.Modules) (D : Divisor ℚ F)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ F) (h : IsPresentation (curveToBase ℚ) L D φ) :
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback (fieldLift σ).inv).obj L, U) →+ F,
      IsPresentation (curveToBase ℚ) ((Scheme.Modules.pullback (fieldLift σ).inv).obj L)
        (σ • D) ψ := by sorry
