-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_dyadic_abelian_picard_family_and_all_base_changes
-- name    : MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T08:14:08.645991+00:00
-- url     : https://prove2.me/theorems/c991b004-26f9-4875-8509-7c89b48e5ddd
-- statement:
--   One relative Picard scheme of the actual dyadic mixed quadratic curve and its original zero section represents the original degree-zero subfunctor after every algebra base change. It carries a commutative relative group law, an abelian-scheme structure and a pointed Abel–Jacobi map. The two complete original existence statements retain all compatibility and base-change quantifiers. Named downstream consumer: the actual dyadic Neron model and arithmetic norm extensions.

import Theorems.Thm_MazurTransfer_order13_actual_dyadic_integral_picard_representation_original
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019

theorem MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes : (∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase) ∧ (∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (_ : RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D)
      (L : RelativeGroupLaw BaseRing D.toBase)
      (aj : SchemeHomOver (curveToBase BaseRing) D.toBase),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (.of BaseRing)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (.of BaseRing)))).val = D.zeroSection ∧
      (zeroSection).val ≫ aj.val = D.zeroSection ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase) := by sorry
