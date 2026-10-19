-- Prove2me | Theorems.Thm_MazurTransfer_DivisorPresentationRestrictionPublic_presentation_restrict
-- name    : MazurTransfer.DivisorPresentationRestrictionPublic.presentation_restrict
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:42:46.53284+00:00
-- url     : https://prove2.me/theorems/17bbb1eb-8b93-4453-9df6-bb05911c0b58
-- title:
--   Full divisor presentations transport under compatible open restriction and field action
-- statement:
--   Let $C$ be an integral scheme over a field $K$, let $f:C\to C$ be an open immersion, and let $\sigma$ be a $K$-automorphism of its function field. Assume the specified scalar-germ compatibility and equality of the associated place sets on every open. A full divisor presentation of an $\mathcal O_C$-module $L$ by $D$ transports to a full presentation of $L|_f$ by $\sigma D$. Its section map is exactly $$\varphi^{\mathrm{new}}_U=\sigma\circ\varphi_{f(U)}\circ r_U,$$ where $r_U$ is the original restriction-section isomorphism.
-- source:
--   Original complete presentation_restrict contract and proof from MazurTheorem DivisorPresentationRestrictionFieldAction.lean, Apache-2.0, Vas and contributors. Every original binder and hypothesis is explicit; the public preamble contains imports and scopes only. The original section-map constructor is supplied by a separate public checked Definition. The complete original kernel type and constructor type/value are compared. No mathematical hypothesis, conclusion or proof body changes. Earlier formatting attempts failed only in the platform comparison parser and receive no public proof credit. Named downstream consumer: generic curve-isomorphism presentation pullback and actual arithmetic Picard naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: divisor presentations transport along an open-immersion
restriction when the generic field action and open-place sets agree.
Named downstream consumer: actual diamond inverse pullback and comparison
of represented Picard points with arithmetic divisor classes.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationRestrictionSectionMapData
import Theorems.Thm_MazurTransfer_GenericCurveImageSectionMapCompatibility_germToFunctionField_appIso_inv
import Theorems.Thm_MazurTransfer_DivisorSectionSpaceFieldAction_image_lSpaceOn
noncomputable section
universe u
open MazurTransfer
open MazurTransfer.DivisorPresentationRestrictionFieldAction
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue

theorem MazurTransfer.DivisorPresentationRestrictionPublic.presentation_restrict {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) (f : C ⟶ C) [IsOpenImmersion f]
    (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
    (L : C.Modules) (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hfield : ∀ (U : C.Opens) [Nonempty U] (a : Γ(C, U)),
      σ (algebraMap Γ(C, f ''ᵁ U) C.functionField ((f.appIso U).inv a)) =
        algebraMap Γ(C, U) C.functionField a)
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens, placesOf c U =
      (fun v : Place K C.functionField => σ • v) '' placesOf c (f ''ᵁ U)) :
    letI := (baseToFunctionField c).toAlgebra;
    IsPresentation c (L.restrict f) (σ • D) (restrictionSectionMap c f σ L φ) := by sorry
