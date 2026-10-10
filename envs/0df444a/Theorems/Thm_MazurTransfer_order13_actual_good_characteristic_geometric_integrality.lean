-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
-- name    : MazurTransfer.order13_actual_good_characteristic_geometric_integrality
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T16:28:19.569895+00:00
-- url     : https://prove2.me/theorems/a1bbe32d-e95e-45f4-9f31-990992902454
-- title:
--   Actual order-13 curve is geometrically integral over every perfect good-characteristic field
-- statement:
--   Let K be a perfect field in which 104 is nonzero. Let C/K be the literal two-chart smooth proper curve given by y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1 and its reciprocal chart z = x⁻¹, w = yx⁻³. Then C → Spec(K) is geometrically integral: every field extension gives an integral curve. This includes the actual order-13 curves over F3 and F5. All geometry and the universal constant-global-functions input are derived from the actual curve; no curve model, genus, Picard representation or Jacobian comparison is assumed. The finite-field divisor-class/Jacobian dictionary and rational Jacobian arithmetic remain separate obligations.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth.lean . Actual good-characteristic geometry and function-field/genus-two calculations are newly checked bridges using the unchanged WIP curve and original FLT place, cohomology and Riemann–Roch interfaces. Whole original generic smooth/global-functions geometric-integrality proof and its complete regular-stalk dependency closure checked locally. Apache-2.0 attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
open AlgebraicGeometry

theorem MazurTransfer.order13_actual_good_characteristic_geometric_integrality.{u} (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0) :
    GeometricallyIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by sorry
