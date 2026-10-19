-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
-- name    : MetricCodes.Spherical.HigherHierarchy.levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:42.425795+00:00
-- url     : https://prove2.me/theorems/4cf434eb-adb5-41a4-8b58-4965cb804a49
-- title:
--   MetricCodes.Spherical.HigherHierarchy.levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
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
open Set Filter Topology

theorem MetricCodes.Spherical.HigherHierarchy.levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
    {r : ℕ} {s : ℝ} (_hs : 0 ≤ s) (hs' : s < 1)
    (hclosure : FixedLevelCompactifiedCertificateClosure r) :
    LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s) := by sorry
