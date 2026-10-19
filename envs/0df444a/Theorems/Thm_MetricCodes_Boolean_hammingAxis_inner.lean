-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingAxis_inner
-- name    : MetricCodes.Boolean.hammingAxis_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/dc792075-cd8e-4ff3-8409-e5629f7f7c2a
-- title:
--   MetricCodes.Boolean.hammingAxis_inner
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}

theorem MetricCodes.Boolean.hammingAxis_inner {n : ℕ} (hn : 0 < n)
    (x y : BinaryWord n) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (hammingAxis x) (hammingAxis y) =
        MetricCodes.hammingCorrelation x y := by sorry
