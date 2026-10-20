-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_continuous
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:34.786068+00:00
-- url     : https://prove2.me/theorems/27f25f88-9dec-43bb-8d69-9a483dc503ab
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_continuous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.angularQuadratic_continuous (R : ℝ) :
    Continuous (angularQuadratic R) := by sorry
