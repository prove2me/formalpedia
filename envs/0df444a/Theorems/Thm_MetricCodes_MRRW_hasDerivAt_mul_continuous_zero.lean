-- Prove2me | Theorems.Thm_MetricCodes_MRRW_hasDerivAt_mul_continuous_zero
-- name    : MetricCodes.MRRW.hasDerivAt_mul_continuous_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/07c68f7e-f51e-4ca7-9c43-1b9bdf7a7ba8
-- title:
--   MetricCodes.MRRW.hasDerivAt_mul_continuous_zero
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

theorem MetricCodes.MRRW.hasDerivAt_mul_continuous_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by sorry
