-- Prove2me | Theorems.Thm_MetricCodes_Johnson_mrrwG_variance
-- name    : MetricCodes.Johnson.mrrwG_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:24.606098+00:00
-- url     : https://prove2.me/theorems/e31fe653-ef00-4f8e-be34-249aee3d175e
-- title:
--   MetricCodes.Johnson.mrrwG_variance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

theorem MetricCodes.Johnson.mrrwG_variance {u : ℝ}
    (hu : u ≤ (1 : ℝ) / 2) :
    mrrwG (4 * u * (1 - u)) = MetricCodes.binaryEntropy u := by sorry
