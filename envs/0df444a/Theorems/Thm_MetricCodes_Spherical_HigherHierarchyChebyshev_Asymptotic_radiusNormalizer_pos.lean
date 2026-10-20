-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusNormalizer_pos
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/646424ff-e17e-47a0-b083-f81f64b260be
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_pos
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
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_pos {R : ℝ} (hR : 0 ≤ R) :
    0 < radiusNormalizer R := by sorry
