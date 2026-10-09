-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_quadratic_extension_field_points
-- name    : MazurTransfer.order13_actual_quadratic_extension_field_points
-- status  : Open
-- author  : @Vas
-- created : 2026-10-09T11:58:50.355075+00:00
-- url     : https://prove2.me/theorems/52a0052d-2eb9-41e4-a65b-fe0a12398b7d
-- title:
--   Actual order-13 curve: extension-field point coordinates and exact F9/F25 counts
-- statement:
--   For every field extension K/R, the sections Spec K → C_R over the specified map Spec K → Spec R are in bijection with affine solutions of the sextic equation together with the normalized infinity directions η²=1. In particular, let F9=F3[ω]/(ω²−2) and F25=F5[ω]/(ω²−2). These are genuine fields of cardinalities 9 and 25, because 2 is a nonsquare in each base field. The actual F3 curve has exactly eight points over F9, and the actual F5 curve has exactly twelve points over F25. These extension-field counts are the arithmetic input for degree-two place and divisor enumeration. No Picard-group cardinality or rational Jacobian rank is inferred by this theorem.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Reuses the complete unchanged mathematical finite-field certificates, via an exact equivalence with Mathlib QuadraticAlgebra. Actual two-chart curve geometry integrates official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Full source and Apache-2.0 provenance are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open AlgebraicGeometry CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 5, r ^ 2 ≠ (2 : ZMod 5) + 0 * r) := ⟨by decide⟩

theorem MazurTransfer.order13_actual_quadratic_extension_field_points.{u} :
    (∀ (R K : Type u) [Field R] [Field K] [Algebra R K],
      Nonempty ((MazurTorsion.XOneThirteenAffineCurve.Solution R K ⊕ {η : K // η ^ 2 = 1}) ≃
        NeronModelInfra.SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R))) ∧
    Nat.card (QuadraticAlgebra (ZMod 3) 2 0) = 9 ∧
    Nat.card (QuadraticAlgebra (ZMod 5) 2 0) = 25 ∧
    Nat.card (NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 3) (QuadraticAlgebra (ZMod 3) 2 0))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))) = 8 ∧
    Nat.card (NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 5) (QuadraticAlgebra (ZMod 5) 2 0))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))) = 12 := by sorry
