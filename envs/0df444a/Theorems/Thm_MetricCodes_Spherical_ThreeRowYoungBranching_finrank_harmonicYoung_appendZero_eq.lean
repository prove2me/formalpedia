-- Prove2me | Theorems.Thm_MetricCodes_Spherical_ThreeRowYoungBranching_finrank_harmonicYoung_appendZero_eq
-- name    : MetricCodes.Spherical.ThreeRowYoungBranching.finrank_harmonicYoung_appendZero_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/689104e0-65ef-43e8-a221-db8d31575745
-- title:
--   MetricCodes.Spherical.ThreeRowYoungBranching.finrank_harmonicYoung_appendZero_eq
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
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.ThreeRowYoungBranching
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem MetricCodes.Spherical.ThreeRowYoungBranching.finrank_harmonicYoung_appendZero_eq {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (appendZeroWeight mu)) =
      Module.finrank ℝ (HarmonicYoungSpace (n := n) mu) := by sorry
