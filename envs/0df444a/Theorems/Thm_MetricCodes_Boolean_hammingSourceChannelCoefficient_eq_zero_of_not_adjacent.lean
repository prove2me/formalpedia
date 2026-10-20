-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
-- name    : MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/3ba7cb95-95a5-49be-a30b-9c7c5ef0ced4
-- title:
--   MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
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

theorem MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
    (n k L : ℕ)
    (source target : Fin (L - k + 1))
    (hnot : ¬ (target.val + 1 = source.val ∨
      source.val + 1 = target.val)) :
    hammingSourceChannelCoefficient n k L source target = 0 := by sorry
