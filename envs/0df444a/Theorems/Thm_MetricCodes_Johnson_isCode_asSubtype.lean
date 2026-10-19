-- Prove2me | Theorems.Thm_MetricCodes_Johnson_isCode_asSubtype
-- name    : MetricCodes.Johnson.isCode_asSubtype
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/f1fe5e6b-a14e-4b49-8035-388ea646433d
-- title:
--   MetricCodes.Johnson.isCode_asSubtype
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

theorem MetricCodes.Johnson.isCode_asSubtype {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w)
    (hC : IsBinaryCode d C) :
    IsCode d (asSubtype C hweight) := by sorry
