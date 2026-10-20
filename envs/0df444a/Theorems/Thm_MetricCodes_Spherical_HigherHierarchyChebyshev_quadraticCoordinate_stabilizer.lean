-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_stabilizer
-- name    : MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_stabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:31.984834+00:00
-- url     : https://prove2.me/theorems/dab2e8a5-5f02-43c2-91b6-d9308a3bfc96
-- title:
--   MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_stabilizer
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev

theorem MetricCodes.Spherical.HigherHierarchyChebyshev.quadraticCoordinate_stabilizer {R : ℝ} (hR : 0 < R)
    (r : ℕ) (i : Fin r) :
    MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate
      (stabilizer R r i) = zero R (r + 1) (i.val + 1) := by sorry
