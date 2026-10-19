-- Prove2me | Theorems.Thm_MetricCodes_MRRW_rankPenalty_interior
-- name    : MetricCodes.MRRW.rankPenalty_interior
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/6e24fdf6-096f-4868-9851-00257650b32d
-- title:
--   MetricCodes.MRRW.rankPenalty_interior
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

theorem MetricCodes.MRRW.rankPenalty_interior {a u e : ℝ}
    (hweight : 0 < interiorWeight a u e)
    (hweight' : interiorWeight a u e < 1) :
    MetricCodes.Johnson.rankPenalty
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) =
      MetricCodes.binaryEntropy e := by sorry
