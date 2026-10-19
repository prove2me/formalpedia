-- Prove2me | Theorems.Thm_MetricCodes_wordOfSupport_injective
-- name    : MetricCodes.wordOfSupport_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/fe2fa9a1-12e2-4ab8-8f42-6818172240fa
-- title:
--   MetricCodes.wordOfSupport_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset

theorem MetricCodes.wordOfSupport_injective {n : ℕ} :
    Function.Injective (wordOfSupport (n := n)) := by sorry
