-- Prove2me | Theorems.Thm_MetricCodes_Hamming_tendsto_logb_ambientDimension
-- name    : MetricCodes.Hamming.tendsto_logb_ambientDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:21.918845+00:00
-- url     : https://prove2.me/theorems/f7f3e3a1-6d07-4c26-a3ce-552b9e23ce9d
-- title:
--   MetricCodes.Hamming.tendsto_logb_ambientDimension
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

theorem MetricCodes.Hamming.tendsto_logb_ambientDimension {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (ambientDimension n
            (transverseDegree b n) (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by sorry
