-- Prove2me | Theorems.Thm_MetricCodes_MRRW_interior_boundary_weight_gt_distance
-- name    : MetricCodes.MRRW.interior_boundary_weight_gt_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/5fa14397-e607-41a5-a5e1-23a1d10e3cb8
-- title:
--   MetricCodes.MRRW.interior_boundary_weight_gt_distance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology

theorem MetricCodes.MRRW.interior_boundary_weight_gt_distance {δ a u : ℝ}
    (hδ : 0 < δ)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ / 2 < a := by sorry
