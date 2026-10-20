-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingWindowChannelMatrix_pairing
-- name    : MetricCodes.Boolean.hammingWindowChannelMatrix_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/125731ad-94a5-448b-8e6f-7c093fce2807
-- title:
--   MetricCodes.Boolean.hammingWindowChannelMatrix_pairing
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

theorem MetricCodes.Boolean.hammingWindowChannelMatrix_pairing
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (Q R : HammingWindowIndex n k L) :
    (∑ p : Fin n × HammingWindowIndex n k L,
      hammingWindowChannelMatrix n k L v lam p Q *
        hammingWindowChannelMatrix n k L v lam p R) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentBlockCoefficient n k L v lam target R.1) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAdjacentChannel n k L target R.1
            (hammingWindowBasis n k L R)) := by sorry
