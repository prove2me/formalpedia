-- Prove2me | Theorems.Thm_MetricCodes_johnsonAmbientDimension_eq
-- name    : MetricCodes.johnsonAmbientDimension_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/19dd7782-a2e5-4bd0-bbf6-2f3dd79a0851
-- title:
--   MetricCodes.johnsonAmbientDimension_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset

theorem MetricCodes.johnsonAmbientDimension_eq (n a L : ℕ)
    (haL : a ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n a L =
      n.choose L - precedingBinomial n a := by sorry
