-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_degree_two_closed_point_counts
-- name    : MazurTransfer.order13_actual_degree_two_closed_point_counts
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T13:04:49.69532+00:00
-- url     : https://prove2.me/theorems/41eb3b37-1685-465a-9f27-d742c9bcb7f0
-- title:
--   Actual order-13 curve: exhaustive degree-two closed-point counts over F3 and F5
-- statement:
--   Let $C_q$ be the smooth proper two-chart curve over $\mathbb F_q$ obtained from $y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1$ and its reciprocal chart, with transition $z=x^{-1}$ and $w=yx^{-3}$. Write $C_q^{(2)}$ for the set of closed points $x$ satisfying $[\kappa(x):\mathbb F_q]=2$. Then
--
--   $$\lvert C_3^{(2)}\rvert=1,\qquad\lvert C_5^{(2)}\rvert=3.$$
--
--   These are exhaustive counts of degree-two closed points of the actual curve. Together with its rational-point counts, they supply the point data needed to enumerate effective divisors of degree two. Picard-group cardinality, Jacobian rank and rational-point exclusion over $\mathbb Q$ remain separate obligations.
--
--   Formalization Note: residue-field scalars come from the actual curve-to-base morphism. The public proof uses the already proved good-characteristic geometry theorem and preserves the original finite-field arithmetic certificates.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Literal two-chart curve and unchanged finite-field arithmetic certificates reused with Apache-2.0 headers. Compatible scheme, residue-field, and curve infrastructure uses official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The coordinate-kernel, scalar compatibility, residue-lift and exhaustivity bridges are new checked work.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_MazurTransfer_Order13DegreeTwoClosedPoints
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
open AlgebraicGeometry CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem MazurTransfer.order13_actual_degree_two_closed_point_counts :
    Nat.card {x : MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 3) //
      MazurTransfer.Order13FiniteCurvePlaces.DegreeTwoPoint (ZMod 3) x} = 1 ∧
    Nat.card {x : MazurTorsion.XOneThirteenProjectiveCurve.curveScheme (ZMod 5) //
      MazurTransfer.Order13FiniteCurvePlaces.DegreeTwoPoint (ZMod 5) x} = 3 := by sorry
