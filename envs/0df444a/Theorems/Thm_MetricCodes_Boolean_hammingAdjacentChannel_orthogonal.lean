-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_orthogonal
-- name    : MetricCodes.Boolean.hammingAdjacentChannel_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/40626804-1307-4e43-b84e-edfaa3a61149
-- title:
--   MetricCodes.Boolean.hammingAdjacentChannel_orthogonal
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

theorem MetricCodes.Boolean.hammingAdjacentChannel_orthogonal
    (n k L : ℕ)
    (target source other : Fin (L - k + 1))
    (hne : source ≠ other)
    (f g : Function n) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target other g) = 0 := by sorry
