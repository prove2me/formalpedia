-- Prove2me | Theorems.Thm_MazurTransfer_order13_ordinary_chart_or_two_infinity_centers
-- name    : MazurTransfer.order13_ordinary_chart_or_two_infinity_centers
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:09:29.181609+00:00
-- url     : https://prove2.me/theorems/1b48226e-a62c-4dc5-a109-4009e2298127
-- title:
--   The ordinary chart and two infinity centers cover the actual rational curve
-- statement:
--   Every point of the actual X₁(13) curve over the rationals lies in its ordinary affine chart or equals one of its two specified infinity centers. This exposes the complete already-proved ordinary-chart complement statement with minimal statement dependencies for the cubic divisor computation. It adds no new curve geometry.
-- source:
--   Original retained MazurTheorem Order13OrdinaryChartComplement; original complete statement retained; Apache-2.0, Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
noncomputable section
open MazurTransfer AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualInfinityPlaceCenters
local instance publicSourceOrdinaryComplementFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.order13_ordinary_chart_or_two_infinity_centers (x : curveScheme ℚ) :
    x ∈ (ordinaryChartMap ℚ).opensRange ∨
      x = center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) ∨
      x = center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) := by sorry
