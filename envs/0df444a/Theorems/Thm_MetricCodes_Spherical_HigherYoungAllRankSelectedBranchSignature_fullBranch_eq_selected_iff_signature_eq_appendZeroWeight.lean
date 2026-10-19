-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankSelectedBranchSignature_fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
-- name    : MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature.fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/a4d590e6-e92e-46bb-9236-ee0a70087a9b
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature.fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature.fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (nu : FullBranchWeight lam) :
    nu = fullBranchOfInterlaces mu h ↔
      fullBranchSignature nu = appendZeroWeight mu := by sorry
