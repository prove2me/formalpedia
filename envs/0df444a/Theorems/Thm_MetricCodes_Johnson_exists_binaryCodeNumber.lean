-- Prove2me | Theorems.Thm_MetricCodes_Johnson_exists_binaryCodeNumber
-- name    : MetricCodes.Johnson.exists_binaryCodeNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/7b54d34f-cde6-4f85-90e6-46701250ceae
-- title:
--   MetricCodes.Johnson.exists_binaryCodeNumber
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

theorem MetricCodes.Johnson.exists_binaryCodeNumber (n d : ℕ) :
    ∃ C : Finset (BinaryWord n),
      IsBinaryCode d C ∧ C.card = binaryCodeNumber n d := by sorry
