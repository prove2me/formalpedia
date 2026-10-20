-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusNormalizer_quadraticCoordinate
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_quadraticCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:33.730806+00:00
-- url     : https://prove2.me/theorems/f4090d85-96e9-47e5-aef8-bb51b38e3b39
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_quadraticCoordinate
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

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusNormalizer_quadraticCoordinate {a : ℝ} (ha : 0 ≤ a) :
    radiusNormalizer (a * (1 + a)) =
      (2 / Real.pi) * Real.arcsin (1 / (1 + 2 * a)) := by sorry
