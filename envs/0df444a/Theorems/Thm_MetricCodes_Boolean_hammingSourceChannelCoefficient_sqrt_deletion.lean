-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_sqrt_deletion
-- name    : MetricCodes.Boolean.hammingSourceChannelCoefficient_sqrt_deletion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/228b5b56-fa95-4c8b-bf48-a18901a125fa
-- title:
--   MetricCodes.Boolean.hammingSourceChannelCoefficient_sqrt_deletion
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

theorem MetricCodes.Boolean.hammingSourceChannelCoefficient_sqrt_deletion
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (source target : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val) :
    Real.sqrt (hammingSourceChannelCoefficient n k L source target) =
      (Real.sqrt (n : ℝ))⁻¹ *
        (Real.sqrt (k + source.val : ℝ))⁻¹ *
          Real.sqrt (harmonicCoefficient n k source.val) := by sorry
