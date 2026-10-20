-- Prove2me | Theorems.Thm_MetricCodes_hammingDist_binaryTranslate
-- name    : MetricCodes.hammingDist_binaryTranslate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/c0ac1278-a357-4d6f-a420-9092d3aaa463
-- title:
--   MetricCodes.hammingDist_binaryTranslate
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset

theorem MetricCodes.hammingDist_binaryTranslate {n : ℕ} (z x y : BinaryWord n) :
    hammingDist (binaryTranslate z x) (binaryTranslate z y) =
      hammingDist x y := by sorry
