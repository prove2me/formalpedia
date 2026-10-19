-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_isometry
-- name    : MetricCodes.Boolean.hammingAdjacentChannel_isometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/d1dbdfee-01da-4337-9a8b-9ddeee32abf4
-- title:
--   MetricCodes.Boolean.hammingAdjacentChannel_isometry
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

theorem MetricCodes.Boolean.hammingAdjacentChannel_isometry
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (target source : Fin (L - k + 1))
    (hadjacent : target.val + 1 = source.val ∨
      source.val + 1 = target.val)
    (f g : Function n) (hf : IsLevel (k + source.val) f) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAdjacentChannel n k L target source g) =
      dot f g := by sorry
