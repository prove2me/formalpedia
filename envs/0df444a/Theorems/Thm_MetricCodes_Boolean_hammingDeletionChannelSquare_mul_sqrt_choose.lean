-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingDeletionChannelSquare_mul_sqrt_choose
-- name    : MetricCodes.Boolean.hammingDeletionChannelSquare_mul_sqrt_choose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/74d95795-3a68-4dc4-a8d5-62fec12fcf06
-- title:
--   MetricCodes.Boolean.hammingDeletionChannelSquare_mul_sqrt_choose
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

theorem MetricCodes.Boolean.hammingDeletionChannelSquare_mul_sqrt_choose
    {n k i : ℕ} (hn : 0 < n)
    (_ : k ≤ i) (hboundary : i + k < n) :
    hammingDeletionChannelSquare n k i *
        Real.sqrt (n.choose i : ℝ) =
      MetricCodes.hammingJacobiEntry n k i *
        Real.sqrt (n.choose (i + 1) : ℝ) := by sorry
