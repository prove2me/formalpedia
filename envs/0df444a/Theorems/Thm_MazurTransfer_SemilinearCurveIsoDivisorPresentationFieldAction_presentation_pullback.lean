-- Prove2me | Theorems.Thm_MazurTransfer_SemilinearCurveIsoDivisorPresentationFieldAction_presentation_pullback
-- name    : MazurTransfer.SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T13:35:42.902318+00:00
-- url     : https://prove2.me/theorems/0734ef24-a7b0-44b0-b2ce-2d3c2da18a78
-- title:
--   Semilinear curve-isomorphism pullback transports full divisor presentations
-- statement:
--   For an integral curve with a specified semilinear function-field automorphism, inverse curve-isomorphism pullback transports a complete divisor presentation when the original generic-stalk and place-action diagrams hold. Every original premise and the complete original universe telescope are retained.
-- source:
--   MazurTheorem SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback; the complete original FLT divisor-presentation predicate and isomorphism transport are reused through their registered exact original interface, Apache-2.0, official pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Definitions.Def_MazurTransfer_SemilinearDivisorPresentationRestrictionSectionMapOriginalData20261018
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
variable (g : letI := (baseToFunctionField c).toAlgebra; SemilinearAut K C.functionField)

theorem MazurTransfer.SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback (L : C.Modules)
    (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hgeneric : letI := (baseToFunctionField c).toAlgebra; C.fromSpecStalk (genericPoint C) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (SemilinearAut.toRingAut g).toRingHom) ≫ C.fromSpecStalk (genericPoint C))
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => g • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback e.inv).obj L, U) →+ (C.functionField : Type u),
      IsPresentation c ((Scheme.Modules.pullback e.inv).obj L) (g • D) ψ := by sorry
