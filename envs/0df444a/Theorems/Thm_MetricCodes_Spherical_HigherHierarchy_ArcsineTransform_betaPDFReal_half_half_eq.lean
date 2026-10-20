-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_betaPDFReal_half_half_eq
-- name    : MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.betaPDFReal_half_half_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:30.752311+00:00
-- url     : https://prove2.me/theorems/82ca86ab-f098-4bef-a3a0-06cb2e65f0e2
-- title:
--   MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.betaPDFReal_half_half_eq
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

theorem MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.betaPDFReal_half_half_eq (u : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u =
      (1 / Real.pi) * (Real.sqrt (u * (1 - u)))⁻¹ := by sorry
