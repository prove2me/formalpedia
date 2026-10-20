-- Prove2me | Theorems.Thm_MetricCodes_MRRW_variationalRate_lt_mrrw_of_interior
-- name    : MetricCodes.MRRW.variationalRate_lt_mrrw_of_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:26.055068+00:00
-- url     : https://prove2.me/theorems/d2197651-6703-40b2-80fe-cdd959b474e3
-- title:
--   MetricCodes.MRRW.variationalRate_lt_mrrw_of_interior
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

theorem MetricCodes.MRRW.variationalRate_lt_mrrw_of_interior
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ < MetricCodes.Hamming.classicalRate δ) :
    MetricCodes.Johnson.variationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by sorry
