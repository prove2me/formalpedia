-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
-- name    : MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:52.737619+00:00
-- url     : https://prove2.me/theorems/fb99bda2-3872-4d50-8880-9b5fdadcefc9
-- title:
--   MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
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
set_option autoImplicit false

theorem MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedHierarchyInf_of_compactification
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤
      sInf (Set.range fun r : ℕ =>
        MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
          (levelRate r) s) := by sorry
