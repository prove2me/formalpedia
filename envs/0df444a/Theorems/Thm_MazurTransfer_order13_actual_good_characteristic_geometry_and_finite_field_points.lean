-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
-- name    : MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T11:30:12.021759+00:00
-- url     : https://prove2.me/theorems/0f52500e-7873-40bb-a5a6-5404979499c0
-- title:
--   Actual order-13 curve: smooth proper geometry and six rational points over F3 and F5
-- statement:
--   Let $C_K$ be the literal two-chart curve $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$, glued to its reciprocal chart by $z=x^{-1}$, $w=yx^{-3}$. Over every field $K$ with $104\ne0$, this actual scheme is integral, proper and Noetherian, and its structure morphism is smooth of relative dimension one. In particular this applies over the fields with three and five elements. The actual scheme-valued rational sections over each of these two prime fields have cardinality exactly six. The counts are obtained through an explicit equivalence of the actual scheme points with the existing WIP affine solution and infinity-direction certificates. No geometric Picard-group cardinality, Jacobian rank, reduction map, modular identification, rational-point exclusion over Q, or full Mazur classification is asserted.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Reuses the unchanged finite-field certificate file, with all its mathematical declarations preserved. Actual two-chart geometry and Cech/Picard integration use official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Apache-2.0 headers and source provenance retained. The full public proof embeds the genuine point-coordinate/gluing equivalence and the explicit polynomial separability certificates.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open AlgebraicGeometry CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.{u} :
    (∀ (K : Type u) [Field K], (104 : K) ≠ 0 →
      IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) ∧
      SmoothOfRelativeDimension 1 (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ∧
      IsProper (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ∧
      IsNoetherian (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K)) ∧
    Nat.card (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of (ZMod 3))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))) = 6 ∧
    Nat.card (NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of (ZMod 5))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))) = 6 := by sorry
