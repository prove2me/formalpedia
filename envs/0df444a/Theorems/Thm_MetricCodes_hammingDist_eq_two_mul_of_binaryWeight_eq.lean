-- Prove2me | Theorems.Thm_MetricCodes_hammingDist_eq_two_mul_of_binaryWeight_eq
-- name    : MetricCodes.hammingDist_eq_two_mul_of_binaryWeight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/f165afc9-e52b-44c8-99a6-caf1655c3635
-- title:
--   MetricCodes.hammingDist_eq_two_mul_of_binaryWeight_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset

theorem MetricCodes.hammingDist_eq_two_mul_of_binaryWeight_eq {n : ℕ}
    (x y : BinaryWord n) (hweight : binaryWeight x = binaryWeight y) :
    hammingDist x y = 2 * (wordSupport x \ wordSupport y).card := by sorry
