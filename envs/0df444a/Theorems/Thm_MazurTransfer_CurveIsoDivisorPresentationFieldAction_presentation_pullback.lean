-- Prove2me | Theorems.Thm_MazurTransfer_CurveIsoDivisorPresentationFieldAction_presentation_pullback
-- name    : MazurTransfer.CurveIsoDivisorPresentationFieldAction.presentation_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:54:28.472242+00:00
-- url     : https://prove2.me/theorems/59a40273-1ac0-4f16-820c-ad7c261b052d
-- title:
--   A compatible curve isomorphism pulls back full divisor presentations by the field action
-- statement:
--   Let $C$ be an integral scheme over a field $K$, let $e:C\simeq C$ be an isomorphism, and let $\sigma$ be the specified $K$-automorphism of its function field. Assume the original compatibility of the inverse curve morphism with the generic-stalk action and with place sets on every open. Every full divisor presentation of an $\mathcal O_C$-module $L$ by $D$ then induces a full divisor presentation of $(e^{-1})^*L$ by $\sigma D$. This is the original pullback contract used for arithmetic Picard naturality.
-- source:
--   Original complete presentation_pullback contract and proof, with original places_image_of_preimage helper, from MazurTheorem CurveIsoDivisorPresentationFieldAction.lean, Apache-2.0, Vas and contributors. All original binders and hypotheses are explicit. The original restriction dependency is qualified by its exact-original public contract DivisorPresentationRestrictionPublic.presentation_restrict; all mathematical proof steps are retained. The full original closed type is kernel-compared. Named downstream consumer: Order13ActualCurveDivisorPresentationPullback.presentation_pullback and actual arithmetic Picard curve-pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve pullback transports full divisor presentations
when its actual generic-stalk and place actions match a field automorphism.
Named downstream consumer: the actual order-thirteen curve over Q and the
arithmetic Picard action comparison.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Theorems.Thm_MazurTransfer_DivisorPresentationRestrictionPublic_presentation_restrict
import Theorems.Thm_MazurTransfer_GenericCurveImageSectionMapCompatibility_germToFunctionField_appIso_inv
noncomputable section
universe u
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue

theorem MazurTransfer.CurveIsoDivisorPresentationFieldAction.presentation_pullback {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
    (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
    (L : C.Modules)
    (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ e.inv =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ C.fromSpecStalk (genericPoint C))
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => σ • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra;
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback e.inv).obj L, U) →+ (C.functionField : Type u),
      IsPresentation c ((Scheme.Modules.pullback e.inv).obj L) (σ • D) ψ := by sorry
