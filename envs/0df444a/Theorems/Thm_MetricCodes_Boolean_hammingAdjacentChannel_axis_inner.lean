-- Prove2me | Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_axis_inner
-- name    : MetricCodes.Boolean.hammingAdjacentChannel_axis_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:18.697767+00:00
-- url     : https://prove2.me/theorems/09f26917-dcd8-473b-8d1c-5f78edeed99a
-- title:
--   MetricCodes.Boolean.hammingAdjacentChannel_axis_inner
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

theorem MetricCodes.Boolean.hammingAdjacentChannel_axis_inner
    {n k L : ℕ} (hn : 0 < n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (x : BinaryWord n)
    (target source : Fin (L - k + 1))
    (f h : Function n) (hh : IsHarmonic k h) :
    coordinateDot
      (hammingAdjacentChannel n k L target source f)
      (hammingAxisTensor x (wordHarmonicEmbedding x k target.val h)) =
      Real.sqrt (hammingSourceChannelCoefficient n k L source target) *
        dot f (wordHarmonicEmbedding x k source.val h) := by sorry
