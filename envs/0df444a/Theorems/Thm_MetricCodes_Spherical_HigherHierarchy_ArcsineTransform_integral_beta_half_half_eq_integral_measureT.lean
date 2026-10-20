-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_integral_beta_half_half_eq_integral_measureT
-- name    : MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_beta_half_half_eq_integral_measureT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:30.752311+00:00
-- url     : https://prove2.me/theorems/6f109c6c-1e28-4748-bb61-925af742c5b5
-- title:
--   MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_beta_half_half_eq_integral_measureT
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology
open MetricCodes.Spherical.HigherHierarchy.ArcsineTransform

theorem MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_beta_half_half_eq_integral_measureT (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) =
      (1 / Real.pi) *
        ∫ z, f ((z + 1) / 2) ∂Polynomial.Chebyshev.measureT := by sorry
