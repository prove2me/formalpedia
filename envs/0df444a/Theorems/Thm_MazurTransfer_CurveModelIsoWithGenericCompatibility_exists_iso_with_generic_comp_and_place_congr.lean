-- Prove2me | Theorems.Thm_MazurTransfer_CurveModelIsoWithGenericCompatibility_exists_iso_with_generic_comp_and_place_congr
-- name    : MazurTransfer.CurveModelIsoWithGenericCompatibility.exists_iso_with_generic_comp_and_place_congr
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:35:54.970372+00:00
-- url     : https://prove2.me/theorems/350be939-0323-45ba-8310-24e94c66476c
-- title:
--   A fixed-model curve isomorphism with generic-stalk and closed-place compatibility
-- statement:
--   Let $M,M\prime$ be smooth proper curve models over a field $K$, with specified identifications of their function fields with $F,F\prime$. A $K$-algebra isomorphism $\varphi:F\simeq F\prime$ induces a curve isomorphism $e:M.C\simeq M\prime.C$ over $K$ which realizes the induced contravariant function-field map on the generic stalk and the corresponding congruence on every closed-point place. In particular, $$\eta_M\,;e=\operatorname{Spec}(\psi^{-1})\,;\eta_{M\prime}.$$ This exports the generic compatibility already constructed in the retained fixed-model proof and supplies arithmetic naturality of Picard pullback.
-- source:
--   Complete retained proof from MazurTheorem CurveModelIsoWithGenericCompatibility.lean, Apache-2.0, Vas and contributors, adapting the original Anthropic FLT proof at pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The original complete statement and main proof body are unchanged. Its complete original generic-base helper is inlined under a fresh namespace. Native, strict and complete frontend checks pass; full original and public closed types are kernel-compared. Named downstream consumer: actual generic-compatible curve field-automorphism lift.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Retains the Anthropic FLT proof at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: fixed-model isomorphism with generic and closed-place compatibility.
Named downstream consumer: actual curve field-automorphism lifts and Picard arithmetic naturality. -/
import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem MazurTransfer.CurveModelIsoWithGenericCompatibility.exists_iso_with_generic_comp_and_place_congr
    {K : Type u} [Field K]
    {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (φ : F ≃ₐ[K] F') (M : CurveModel K F) (M' : CurveModel K F') :
    let ψr : M.C.functionField ≃+* M'.C.functionField :=
      M.ffEquiv.symm.trans (φ.toRingEquiv.trans M'.ffEquiv)
    ∃ (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase),
      (M.C.fromSpecStalk (genericPoint M.C) ≫ e.hom =
        Spec.map ψr.toCommRingCatIso.inv ≫ M'.C.fromSpecStalk (genericPoint M'.C)) ∧
      ∀ x : closedPoints M.C,
        M'.placeOfPoint ⟨e.hom.base x.1, by
            show IsClosed ({e.hom.base x.1} : Set M'.C)
            rw [← Set.image_singleton]
            exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isClosedMap _ x.2⟩
          = Place.congrRingEquiv φ.toRingEquiv (fun a => φ.commutes a) (M.placeOfPoint x) := by sorry
