-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_relativeEntropy_eq_log_pi_sub_one_of_density
-- name    : MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_relativeEntropy_eq_log_pi_sub_one_of_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/a3808df3-37f4-4ec9-af73-d21a0892c0be
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_relativeEntropy_eq_log_pi_sub_one_of_density
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

theorem MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_relativeEntropy_eq_log_pi_sub_one_of_density
    (hdensity : comparisonMeasure.rnDeriv arcsineMeasure =ᵐ[arcsineMeasure]
      fun t => ENNReal.ofReal (Real.pi * Real.sqrt t))
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure)
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1 := by sorry
