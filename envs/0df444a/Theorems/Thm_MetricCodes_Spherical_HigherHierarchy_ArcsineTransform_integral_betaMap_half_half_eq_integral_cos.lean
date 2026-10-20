-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_integral_betaMap_half_half_eq_integral_cos
-- name    : MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_betaMap_half_half_eq_integral_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/d5353516-00ff-4991-b4e9-be97d68175ab
-- title:
--   MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_betaMap_half_half_eq_integral_cos
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

theorem MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_betaMap_half_half_eq_integral_cos
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        (1 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi, f ((Real.cos θ + 1) / 8) := by sorry
