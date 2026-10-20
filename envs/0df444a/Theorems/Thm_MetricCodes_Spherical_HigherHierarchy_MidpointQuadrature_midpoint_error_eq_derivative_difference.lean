-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_MidpointQuadrature_midpoint_error_eq_derivative_difference
-- name    : MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpoint_error_eq_derivative_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/e3306125-a549-478d-9a43-bcfcba87f4e2
-- title:
--   MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpoint_error_eq_derivative_difference
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature

theorem MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpoint_error_eq_derivative_difference
    {f g : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hf : ContinuousOn f (Set.Icc x y))
    (hderiv : ∀ z ∈ Set.Ioo x y, HasDerivAt f (g z) z) :
    ∃ u ∈ Set.Ioo x ((x + y) / 2),
      ∃ v ∈ Set.Ioo ((x + y) / 2) y,
        f ((x + y) / 2) - (f x + f y) / 2 =
          ((y - x) / 4) * (g u - g v) := by sorry
