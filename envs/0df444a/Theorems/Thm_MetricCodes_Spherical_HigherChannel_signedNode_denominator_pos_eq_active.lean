-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherChannel_signedNode_denominator_pos_eq_active
-- name    : MetricCodes.Spherical.HigherChannel.signedNode_denominator_pos_eq_active
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/dc7c1841-a1ce-4f64-90ca-22c97ea374d2
-- title:
--   MetricCodes.Spherical.HigherChannel.signedNode_denominator_pos_eq_active
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherChannel.signedNode_denominator_pos_eq_active {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Bool)).erase (ℓ, true),
      (L ℓ - signedNode L z)) = activeDenominator L ℓ := by sorry
