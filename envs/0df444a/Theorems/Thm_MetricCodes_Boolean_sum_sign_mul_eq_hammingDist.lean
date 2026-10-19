-- Prove2me | Theorems.Thm_MetricCodes_Boolean_sum_sign_mul_eq_hammingDist
-- name    : MetricCodes.Boolean.sum_sign_mul_eq_hammingDist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/52d4af80-9f31-499f-96da-cb6305668c09
-- title:
--   MetricCodes.Boolean.sum_sign_mul_eq_hammingDist
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

theorem MetricCodes.Boolean.sum_sign_mul_eq_hammingDist
    (x y : BinaryWord n) :
    (∑ a : Fin n, sign (x a) * sign (y a)) =
      (n : ℝ) - 2 * (MetricCodes.hammingDist x y : ℝ) := by sorry
