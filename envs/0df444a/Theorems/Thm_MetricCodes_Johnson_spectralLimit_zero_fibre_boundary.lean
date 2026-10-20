-- Prove2me | Theorems.Thm_MetricCodes_Johnson_spectralLimit_zero_fibre_boundary
-- name    : MetricCodes.Johnson.spectralLimit_zero_fibre_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:23.310643+00:00
-- url     : https://prove2.me/theorems/174ae263-3ab6-4476-a9d5-88bd47d19ed6
-- title:
--   MetricCodes.Johnson.spectralLimit_zero_fibre_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

theorem MetricCodes.Johnson.spectralLimit_zero_fibre_boundary {α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2) :
    1 - spectralLimit α 0 0 u =
      (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by sorry
