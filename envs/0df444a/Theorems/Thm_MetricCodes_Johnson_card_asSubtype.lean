-- Prove2me | Theorems.Thm_MetricCodes_Johnson_card_asSubtype
-- name    : MetricCodes.Johnson.card_asSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/cfa93546-7076-4574-a7b6-a8ab8605797e
-- title:
--   MetricCodes.Johnson.card_asSubtype
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

theorem MetricCodes.Johnson.card_asSubtype {n w : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    (asSubtype C hweight).card = C.card := by sorry
