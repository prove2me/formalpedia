-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_log_integrable_of_logMoment
-- name    : MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_log_integrable_of_logMoment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/2182085c-2d86-4f8d-a1e9-890db9e36ff4
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_log_integrable_of_logMoment
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
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy

theorem MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_log_integrable_of_logMoment
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    Integrable (fun t : ℝ => Real.log t) comparisonMeasure := by sorry
