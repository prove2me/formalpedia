-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_restricted_axisDot
-- name    : MetricCodes.Boolean.hammingAdjacentChannel_restricted_axisDot
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:20.207146+00:00
-- url     : https://prove2.me/theorems/c333fe59-3dfa-4a98-8013-80116fb8cc1f
-- title:
--   MetricCodes.Boolean.hammingAdjacentChannel_restricted_axisDot
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

theorem MetricCodes.Boolean.hammingAdjacentChannel_restricted_axisDot
    (n k L : ℕ) (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f g : Function n)
    (hf : IsLevel (k + source.val) f)
    (hg : IsLevel (k + target.val) g) :
    (∑ a : Fin n,
      ∑ S : Level n (k + target.val),
        hammingAdjacentChannel n k L target source f a S.val *
          (hammingAxis x a * g S.val)) =
      coordinateDot
        (hammingAdjacentChannel n k L target source f)
        (hammingAxisTensor x g) := by sorry
