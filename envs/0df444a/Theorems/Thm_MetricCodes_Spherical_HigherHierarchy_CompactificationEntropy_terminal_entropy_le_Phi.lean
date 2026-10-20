-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_terminal_entropy_le_Phi
-- name    : MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.terminal_entropy_le_Phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:40.58935+00:00
-- url     : https://prove2.me/theorems/6354efe9-124b-445f-8e52-87477de0dae3
-- title:
--   MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.terminal_entropy_le_Phi
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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy

theorem MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.terminal_entropy_le_Phi {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    MetricCodes.sphericalEntropy (a (Fin.last r)) ≤ Phi a b := by sorry
