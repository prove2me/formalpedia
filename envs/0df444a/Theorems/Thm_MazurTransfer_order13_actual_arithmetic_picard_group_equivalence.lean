-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_arithmetic_picard_group_equivalence
-- name    : MazurTransfer.order13_actual_arithmetic_picard_group_equivalence
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T20:52:54.359534+00:00
-- url     : https://prove2.me/theorems/55cfb65c-b234-43c1-960d-030a8825b621
-- title:
--   Actual order-13 Picard points and arithmetic divisor classes: group equivalence over perfect fields
-- statement:
--   For every perfect field of characteristic not dividing 104 and every actual rational section of the literal order-13 curve, construct its represented Picard scheme and a group isomorphism from its actual base-field points to the degree-zero arithmetic divisor class group of its literal function field. The scheme, its group law, and the correspondence are constructed, with arbitrary closed points included. No algebraic-closure assumption, additional presentation input, or chosen-cover hypothesis is imposed.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Official Anthropic FLT Picard, valuation, invertible-sheaf presentation and cohomology arguments at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Perfect-field arithmetic adaptations and the actual group-equivalence bridge are locally kernel and full-source audited before publication.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem MazurTransfer.order13_actual_arithmetic_picard_group_equivalence.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).1
    letI : Algebra K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField :=
      (baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
    ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
      (h : RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D),
      letI := (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε).toSubPicCondition D from h).grpObj
      Nonempty ((Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) ≃*
        Multiplicative (Pic0 K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField)) := by sorry
