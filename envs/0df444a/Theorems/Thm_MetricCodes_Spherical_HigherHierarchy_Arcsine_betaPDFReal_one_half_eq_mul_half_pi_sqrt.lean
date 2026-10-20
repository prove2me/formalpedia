-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_betaPDFReal_one_half_eq_mul_half_pi_sqrt
-- name    : MetricCodes.Spherical.HigherHierarchy.Arcsine.betaPDFReal_one_half_eq_mul_half_pi_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:30.752311+00:00
-- url     : https://prove2.me/theorems/a0ce756b-1132-4d40-abaa-68ec85915f01
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Arcsine.betaPDFReal_one_half_eq_mul_half_pi_sqrt
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
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine

theorem MetricCodes.Spherical.HigherHierarchy.Arcsine.betaPDFReal_one_half_eq_mul_half_pi_sqrt (t : ℝ) :
    betaPDFReal 1 (1 / 2 : ℝ) t =
      betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) t *
        (Real.pi / 2 * Real.sqrt t) := by sorry
