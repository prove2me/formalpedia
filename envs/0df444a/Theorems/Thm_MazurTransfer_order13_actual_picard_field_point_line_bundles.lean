-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_picard_field_point_line_bundles
-- name    : MazurTransfer.order13_actual_picard_field_point_line_bundles
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T19:42:40.936895+00:00
-- url     : https://prove2.me/theorems/33f2e180-4e19-4401-bb63-4733a4fa4b05
-- title:
--   Actual order-13 Picard points classify degree-zero line bundles over the base field
-- statement:
--   For every perfect field K with 104 nonzero and every rational rigidifying section of the literal order-13 curve, a represented Picard scheme is constructed. Pulling its Poincare sheaf back to the original curve gives each K-point an invertible sheaf whose Euler characteristic equals that of the structure sheaf over K itself. Two K-points agree exactly when these sheaves are isomorphic. Conversely, every invertible sheaf with this Euler characteristic is obtained from a unique K-point. No algebraic-closure assumption is imposed on K; this applies to F_3 and F_5. The identification with the computed function-field divisor class group, its cardinality 19, and the full Mazur theorem remain separate open obligations.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Official Anthropic FLT relative Picard, field-spectrum triviality, sheaf/cohomology base-change and geometric algebraic equivalence proofs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The proof reuses accepted actual Picard and actual geometric-integrality results.

import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.order13_actual_picard_field_point_line_bundles.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :
    ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
      (h : RepresentsRelSubPic
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D),
      let M := fun a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase =>
        (Scheme.Modules.pullback
          (toProdSpec (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))).obj
          (h.poincare.pullbackAlong a).L
      (∀ a, Scheme.Modules.IsInvertible (M a) ∧
        ∀ 𝒱 : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover,
          (Module.finrank K
            (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) (M a)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) (M a)).H1 =
          (Module.finrank K
            (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
              (𝟙_ (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).Modules)).H0 : ℤ) -
            Module.finrank K
              (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
                (𝟙_ (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).Modules)).H1) ∧
      (∀ a b, Nonempty (M a ≅ M b) ↔ a = b) ∧
      (∀ (𝒱 : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover)
        (N : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).Modules),
        Scheme.Modules.IsInvertible N →
        (Module.finrank K
          (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) N).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) N).H1 =
        (Module.finrank K
          (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
            (𝟙_ (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).Modules)).H0 : ℤ) -
          Module.finrank K
            (𝒱.sectionsOf (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
              (𝟙_ (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).Modules)).H1 →
        ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase,
          Nonempty (M a ≅ N)) := by sorry
