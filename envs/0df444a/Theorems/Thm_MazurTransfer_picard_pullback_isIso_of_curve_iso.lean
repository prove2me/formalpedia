-- Prove2me | Theorems.Thm_MazurTransfer_picard_pullback_isIso_of_curve_iso
-- name    : MazurTransfer.picard_pullback_isIso_of_curve_iso
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T16:03:20.27843+00:00
-- url     : https://prove2.me/theorems/d9aa47a8-7eae-4b73-a361-7e322812a05f
-- title:
--   Re-rigidified Picard pullback by a curve isomorphism is a scheme isomorphism
-- statement:
--   Let a scheme D represent the algebraically trivial rigidified relative Picard functor of a curve C over Spec R. Let e be an automorphism of C over R. Every morphism N from D to itself over R that classifies re-rigidified pullback by e inverse on every test scheme is a scheme isomorphism. The automorphism need not preserve the chosen rigidifying section. Classification on the universal Poincare line bundle identifies N with the genuine Picard inverse-pair isomorphism. The named downstream consumer is the actual diamond group automorphism of the represented Picard scheme of the order-thirteen curve over Q; it is needed before upgrading arithmetic norm identities to scheme endomorphism identities.
-- source:
--   Owned MazurTheorem integration bridge, Apache-2.0. Complete original Picard inverse-pair proof reused from https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections.lean .

import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
universe u

theorem MazurTransfer.picard_pullback_isIso_of_curve_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (e : C ≅ C) (he : e.hom ≫ c = c) (he' : e.inv ≫ c = c)
    (N : SchemeHomOver D.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (postComp N a)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          ((Scheme.Modules.pullback (curveChange e.inv he' t)).obj (h.poincare.pullbackAlong a).L))) :
    IsIso N.1 := by sorry
