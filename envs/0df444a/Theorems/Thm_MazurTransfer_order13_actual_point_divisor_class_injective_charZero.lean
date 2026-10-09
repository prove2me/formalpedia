-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_point_divisor_class_injective_charZero
-- name    : MazurTransfer.order13_actual_point_divisor_class_injective_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T10:26:03.022102+00:00
-- url     : https://prove2.me/theorems/30b6d98f-fd63-4e21-8007-420cf0b4effd
-- title:
--   Injective rational point divisor classes on the actual order-13 curve over every characteristic-zero field
-- statement:
--   Let $K$ be any field of characteristic zero, including $\mathbb Q$, and let $C/K$ be the actual two-chart order-13 curve
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1,$$
--   with reciprocal gluing $z=x^{-1}$ and $w=yx^{-3}$. The scheme is integral. Using its actual function field $K(C)$ and its structural $K$-algebra map, every $K$-rational section $x$ determines a degree-one valuation place $P_x$ whose valuation subring is exactly the image of the stalk at $x$.
--
--   For every chosen $K$-rational basepoint $s$, there exists an injective map from the rational sections to the genuine degree-zero divisor-class group
--   $$x\longmapsto [P_x-P_s]\in\operatorname{Pic}^0(K(C)/K).$$
--   The basepoint maps to zero, and the theorem supplies the exact degree-zero divisor representing each class. Algebraic closedness, Riemann–Roch, a supplied genus datum and injectivity are not additional assumptions. The proof derives the divisor-class injectivity from the actual genus-two Riemann–Roch calculation: a principal difference of distinct degree-one places would supply five independent simple-pole powers in a Riemann–Roch space of dimension three.
--
--   This theorem constructs an injective map into actual function-field divisor classes over $\mathbb Q$. It does not assert a Jacobian rank calculation, the absence of noncuspidal rational points, an identification with a modular curve, or the full Mazur classification. Compatibility with the separately proved scheme-valued Abel–Jacobi map is a further bridge.
-- source:
--   Actual curve and arithmetic by Vas and contributors: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Independently verified official Anthropic FLT function-field and Riemann–Roch development: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The simple-pole power argument adapts P2M/Sol/S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.lean at this immutable pin, to the checked actual genus-two Riemann–Roch space. Apache-2.0 attribution retained. Every characteristic-zero hypothesis is preserved; the concrete construction supplies the generic-stalk places and rational-section injectivity.

import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_finite_H1_of_genusReached
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_omegaSpace_finite_of_genusReached
import Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
open AlgebraicGeometry AlgebraicCurve CategoryTheory

theorem MazurTransfer.order13_actual_point_divisor_class_injective_charZero.{u} (K : Type u) [Field K] [CharZero K] :
    ∃ hC : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K),
      letI := hC
      letI := (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
      ∃ P : {σ : Spec (CommRingCat.of K) ⟶
          MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K //
          σ ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _} →
          Place K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField,
        (∀ x, (P x).deg = 1 ∧
          (algebraMap ((MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).presheaf.stalk
              (x.1 (IsLocalRing.closedPoint K)))
            (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField).range =
            (P x).toValuationSubring.toSubring) ∧
        ∀ s, ∃ cl : {σ : Spec (CommRingCat.of K) ⟶
            MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K //
            σ ≫ MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K = 𝟙 _} →
            Pic0 K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField,
          Function.Injective cl ∧ cl s = 0 ∧
          ∀ x, ∃ Dv : Divisor.degZero (K := K)
              (F := (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField),
            (Dv : Divisor K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField) =
              Finsupp.single (P x) 1 - Finsupp.single (P s) 1 ∧
            cl x = Pic0.mk Dv := by sorry
