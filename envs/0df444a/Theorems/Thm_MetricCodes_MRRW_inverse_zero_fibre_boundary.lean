-- Prove2me | Theorems.Thm_MetricCodes_MRRW_inverse_zero_fibre_boundary
-- name    : MetricCodes.MRRW.inverse_zero_fibre_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/034c9856-76a9-4129-8ee4-a15753767a57
-- title:
--   MetricCodes.MRRW.inverse_zero_fibre_boundary
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
set_option maxHeartbeats 1200000

theorem MetricCodes.MRRW.inverse_zero_fibre_boundary
    {δ r : ℝ}
    (hδ : 0 < δ) (_ : δ < (1 : ℝ) / 2)
    (hr : 0 < r) (hupper : r < 1 - 2 * δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by sorry
