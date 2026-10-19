-- Prove2me | Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos
-- name    : MetricCodes.Hamming.hammingFibreDimension_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/f958874f-8c3b-4931-b78e-f5c04f41bbc8
-- title:
--   MetricCodes.Hamming.hammingFibreDimension_pos
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming

theorem MetricCodes.Hamming.hammingFibreDimension_pos {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < MetricCodes.hammingFibreDimension n k := by sorry
