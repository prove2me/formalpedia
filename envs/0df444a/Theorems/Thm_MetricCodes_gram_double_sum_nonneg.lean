-- Prove2me | Theorems.Thm_MetricCodes_gram_double_sum_nonneg
-- name    : MetricCodes.gram_double_sum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/3c33b00f-73bf-4f13-b5e5-e310f1665772
-- title:
--   MetricCodes.gram_double_sum_nonneg
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem MetricCodes.gram_double_sum_nonneg (C : Finset X) (q : X → E) :
    0 ≤ ∑ x ∈ C, ∑ y ∈ C, ⟪q x, q y⟫_ℝ := by sorry
