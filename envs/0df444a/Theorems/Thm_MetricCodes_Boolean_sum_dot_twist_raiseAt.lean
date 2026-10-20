-- Prove2me | Theorems.Thm_MetricCodes_Boolean_sum_dot_twist_raiseAt
-- name    : MetricCodes.Boolean.sum_dot_twist_raiseAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/ab44e41b-d313-474d-9bc6-30328538fe32
-- title:
--   MetricCodes.Boolean.sum_dot_twist_raiseAt
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

theorem MetricCodes.Boolean.sum_dot_twist_raiseAt
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (raiseAt a g))) =
      dot f (twist x (raise g)) := by sorry
