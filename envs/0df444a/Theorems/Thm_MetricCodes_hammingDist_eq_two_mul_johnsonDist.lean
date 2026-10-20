-- Prove2me | Theorems.Thm_MetricCodes_hammingDist_eq_two_mul_johnsonDist
-- name    : MetricCodes.hammingDist_eq_two_mul_johnsonDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/aca780d0-60d1-45e9-ada2-93dee2aad642
-- title:
--   MetricCodes.hammingDist_eq_two_mul_johnsonDist
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset

theorem MetricCodes.hammingDist_eq_two_mul_johnsonDist {n w : ℕ}
    (x y : JohnsonSphere n w) :
    hammingDist (x : BinaryWord n) (y : BinaryWord n) =
      2 * johnsonDist x y := by sorry
