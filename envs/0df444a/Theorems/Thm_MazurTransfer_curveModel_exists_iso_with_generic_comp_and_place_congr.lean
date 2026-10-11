-- Prove2me | Theorems.Thm_MazurTransfer_curveModel_exists_iso_with_generic_comp_and_place_congr
-- name    : MazurTransfer.curveModel_exists_iso_with_generic_comp_and_place_congr
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T16:34:08.602816+00:00
-- url     : https://prove2.me/theorems/28fb2f86-940c-4b0a-984a-eca0f87da641
-- title:
--   Fixed curve-model isomorphism with generic-stalk and closed-place compatibility
-- statement:
--   A K-algebra isomorphism between the function fields of two fixed smooth proper curve models extends to an isomorphism of those models over Spec K. Its composite with the generic-stalk embedding is exactly the Spec map of the inverse conjugated field isomorphism. On every closed point, the associated place is transported by the original field isomorphism. This simultaneously retains both compatibility properties; no algebraic-closure assumption is added. The named downstream consumer is the actual order-thirteen diamond curve automorphism over Q, its exact order, and the transport of divisor presentations needed to compare the represented Picard action with arithmetic Pic0.
-- source:
--   Owned MazurTheorem integration interface retaining the complete original Anthropic FLT fixed-model isomorphism proof at Apache-2.0 pin 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.lean . The generic-stalk compatibility already proved inside that source is exported alongside its original closed-place conclusion.

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u v w

theorem MazurTransfer.curveModel_exists_iso_with_generic_comp_and_place_congr
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
