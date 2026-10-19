-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualIntegralAbelianPicardFamily_actual_integral_abelian_picard_family
-- name    : MazurTransfer.Order13ActualIntegralAbelianPicardFamily.actual_integral_abelian_picard_family
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T07:48:25.115411+00:00
-- url     : https://prove2.me/theorems/c1fd5790-eb68-4da4-93ca-eb7897d6b35d
-- title:
--   Actual integral abelian Picard family and positive-infinity Abel–Jacobi map
-- statement:
--   Let $R$ be a noetherian commutative integral domain in which $104$ is invertible, and let $C/R$ be the literal order-thirteen curve with positive-infinity section $\varepsilon$. There exist an actual relative Picard designation $D$, a representation of its algebraically trivial rigidified Picard subfunctor, a commutative relative group law $L$ on $D$, and a morphism $\mathrm{AJ}:C\to D$ over $R$. The structure morphism is an abelian scheme in the specified interface, and $$1_L=0_D,\qquad\mathrm{AJ}\circ\varepsilon=0_D.$$ The same designated family has compatible Picard representations after every commutative $R$-algebra base change, and all those structure morphisms are smooth, proper and geometrically connected. This gives a single integral family for the rational Jacobian and its good-characteristic fibres.
-- source:
--   Original complete actual_integral_abelian_picard_family contract and final proof application from MazurTheorem Order13ActualIntegralAbelianPicardFamily.lean, Apache-2.0, Vas and contributors. The three geometric proof inputs alone are replaced by their already Proved public versions, including the stronger relative-dimension theorem. Reuses the newly Proved universal actual Picard family and the original official Anthropic FLT relative group-law and Abel–Jacobi theorem at exact upstream pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The complete original 35611-character closed kernel type is independently exported and compared with both the checked solution and public formal statement, retaining the original group law, actual maps, zero-section equations and all algebra base changes. Native, strict and complete frontend checks pass with standard axioms only. Named downstream consumer: arithmetic good reduction and torsion specialization through this one integral Picard family.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual integral Picard family carries a commutative
relative group law, is an abelian scheme in the original interface, and
has an Abel-Jacobi morphism based at the actual positive infinity section.
The same representing scheme has Picard representations after all algebra
base changes. Named downstream consumer: arithmetic good reduction of the
rational order-13 Jacobian through this single integral family.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardFamilyBaseChanges_actual_integral_picard_family_baseChanges
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_smooth_relative_dimension_one
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer

theorem MazurTransfer.Order13ActualIntegralAbelianPicardFamily.actual_integral_abelian_picard_family (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ (D : RelativePic0Designation R (curveToBase R))
      (_ : RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D)
      (L : RelativeGroupLaw R D.toBase)
      (aj : SchemeHomOver (curveToBase R) D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (.of R)))).val = D.zeroSection ∧
      (Order13IntegralSections.positiveInfinitySection R).val ≫ aj.val = D.zeroSection ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (RepresentsRelSubPic (baseChange R (curveToBase R) A)
          (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R))
          (algEquivZeroCut (baseChange R (curveToBase R) A)
            (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by sorry
