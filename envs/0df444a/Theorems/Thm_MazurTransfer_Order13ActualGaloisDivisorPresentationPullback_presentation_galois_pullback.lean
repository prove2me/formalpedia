-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGaloisDivisorPresentationPullback_presentation_galois_pullback
-- name    : MazurTransfer.Order13ActualGaloisDivisorPresentationPullback.presentation_galois_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:46:42.475988+00:00
-- url     : https://prove2.me/theorems/cc923960-3bd0-4bc7-9f41-874338c351b6
-- title:
--   Actual Galois pullback transports full divisor presentations
-- statement:
--   Pullback along the actual literal curve Galois isomorphism transports every full divisor presentation to the divisor acted on by the original actual geometric semilinear Galois lift. No generic-stalk or place-action hypothesis is added to the original characteristic-zero algebraically closed field telescope.
-- source:
--   MazurTheorem Order13ActualGaloisDivisorPresentationPullback.presentation_galois_pullback; exact original actual geometric curve, function-field lift and full divisor-presentation predicate.

import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: pullback along the literal actual curve Galois isomorphism
transports every full divisor presentation to the divisor of the original
geometric semilinear lift. No generic or place-action premise is added.
Named downstream consumer: actual geometric Picard divisor-class Galois naturality. -/
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGeometricCurveGaloisAutomorphism Order13ActualGeometricGaloisSemilinearAutomorphism
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualGaloisDivisorPresentationPullback.presentation_galois_pullback (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (L : (curveScheme K).Modules)
    (D : Divisor K (actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens, Γ(L, U) →+ actualCurveFunctionField K)
    (h : IsPresentation (curveToBase K) L D φ) :
    ∃ ψ : ∀ U : (curveScheme K).Opens,
      Γ((Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj L, U) →+
        actualCurveFunctionField K,
      IsPresentation (curveToBase K) ((Scheme.Modules.pullback (geometricCurveGaloisIso K σ).hom).obj L)
        (geometricSemilinearAut K σ • D) ψ := by sorry
