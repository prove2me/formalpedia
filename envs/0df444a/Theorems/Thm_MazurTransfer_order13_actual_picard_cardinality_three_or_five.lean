-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_picard_cardinality_three_or_five
-- name    : MazurTransfer.order13_actual_picard_cardinality_three_or_five
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T00:22:30.964893+00:00
-- url     : https://prove2.me/theorems/a6bf25a9-21b9-4aff-ad93-c16355831b3b
-- title:
--   Literal order-13 curve: arithmetic Picard order 19 over Fq for q = 3 or 5
-- statement:
--   For every $q\in\{3,5\}$, let $C_q$ be the literal smooth proper two-chart order-13 curve over $\mathbb F_q$, given by $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal chart. Its genuine degree-zero function-field divisor-class group is finite and has order
--
--   $$|\operatorname{Pic}^0(C_q)|=19.$$
--
--   Its actual function field and structural base algebra are used. The actual geometry, full constant field, genus two, and complete effective degree-two divisor counts are proved inputs. No supplied curve model, genus value, Picard-order dictionary, rational rank, or reduction compatibility is assumed. This is the finite-field arithmetic comparison needed for represented Picard point counts and the later rational Jacobian torsion bound.
-- source:
--   MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The separately checked universal genus-two counting theorem is applied to the accepted literal-curve invariants and exhaustive effective divisor certificates. Headers and attribution retained.

import Mathlib.FieldTheory.Perfect
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem MazurTransfer.order13_actual_picard_cardinality_three_or_five
    (q : ℕ) (hq : q = 3 ∨ q = 5) :
    letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
    let h104 : (104 : ZMod q) ≠ 0 := by rcases hq with rfl | rfl <;> decide
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1
        (ZMod q) h104).1
    letI : Algebra (ZMod q)
        (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField :=
      (AlgebraicCurve.baseToFunctionField
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod q))).toAlgebra
    Finite (AlgebraicCurve.Pic0 (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField) ∧
    Nat.card (AlgebraicCurve.Pic0 (ZMod q)
      (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod q)).functionField) = 19 := by sorry
