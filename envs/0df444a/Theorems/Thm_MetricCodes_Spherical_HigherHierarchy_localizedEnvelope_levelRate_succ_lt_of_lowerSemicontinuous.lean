-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
-- name    : MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/944b0f36-1410-403d-a5ed-8abe6a9f438e
-- title:
--   MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
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

theorem MetricCodes.Spherical.HigherHierarchy.localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlsc : LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s))
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      levelRate (r + 1) t < levelRate r t) :
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate (r + 1)) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by sorry
