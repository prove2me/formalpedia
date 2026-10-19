-- Prove2me | Theorems.Thm_MazurTransfer_GenericCurveImageSectionMapCompatibility_germToFunctionField_appIso_inv
-- name    : MazurTransfer.GenericCurveImageSectionMapCompatibility.germToFunctionField_appIso_inv
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:03:09.904119+00:00
-- url     : https://prove2.me/theorems/d1612a25-f612-402f-8e95-c21126ae4700
-- title:
--   A generic-stalk action determines the inverse section isomorphism on image opens
-- statement:
--   Let $C$ be an integral scheme, $f:C\to C$ an open immersion, and $\sigma:K(C)\to K(C)$ a ring map with the specified compatibility at the generic point. For a nonempty open $U$ and a section $a$ on $U$, applying $\sigma$ to the generic germ of the inverse image-open section isomorphism recovers the original germ: $$\sigma\bigl(\operatorname{germ}_{f(U)}((f_U^\#)^{-1}a)\bigr)=\operatorname{germ}_U(a).$$ This supplies scalar compatibility in divisor-presentation pullback.
-- source:
--   Original complete germToFunctionField_appIso_inv statement and proof, with the unchanged original imageNonempty instance needed to form its type, from MazurTheorem GenericCurveImageSectionMapCompatibility.lean, Apache-2.0, Vas and contributors. The proof uses only Mathlib. The complete original closed type is kernel-compared. The public preamble retains the original image-nonemptiness instance; its native API uses the identical instance already supplied by the accepted cache. Named downstream consumer: DivisorPresentationRestrictionFieldAction.presentation_restrict.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: generic field action agrees with the inverse section
isomorphism on image opens. Named downstream consumer: scalar compatibility
in the restriction/pullback transport of divisor presentations.
-/
import Mathlib
noncomputable section
universe u
namespace MazurTransfer.GenericCurveImageSectionMapCompatibility
open CategoryTheory AlgebraicGeometry
variable {C : Scheme.{u}} [IsIntegral C]

instance imageNonempty (f : C ⟶ C) [IsOpenImmersion f] (U : C.Opens) [Nonempty U] :
    Nonempty (f ''ᵁ U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  exact ⟨⟨f x.1, ⟨x.1, x.2, rfl⟩⟩⟩

end MazurTransfer.GenericCurveImageSectionMapCompatibility
open CategoryTheory AlgebraicGeometry
open MazurTransfer.GenericCurveImageSectionMapCompatibility
variable {C : Scheme.{u}} [IsIntegral C]

theorem MazurTransfer.GenericCurveImageSectionMapCompatibility.germToFunctionField_appIso_inv (f : C ⟶ C) [IsOpenImmersion f]
    (σ : C.functionField ⟶ C.functionField)
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ f =
      Spec.map σ ≫ C.fromSpecStalk (genericPoint C))
    (U : C.Opens) [Nonempty U] (a : Γ(C, U)) :
    σ (C.germToFunctionField (f ''ᵁ U) ((f.appIso U).inv a)) =
      C.germToFunctionField U a := by sorry
