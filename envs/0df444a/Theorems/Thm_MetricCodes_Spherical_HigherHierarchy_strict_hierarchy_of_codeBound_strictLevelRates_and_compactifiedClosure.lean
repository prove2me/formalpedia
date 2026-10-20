-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
-- name    : MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:52.737619+00:00
-- url     : https://prove2.me/theorems/c9d1c373-8c8c-491b-a6b8-b6c7916b9dd7
-- title:
--   MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
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

theorem MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
    (hcode : FixedLevelHierarchyCodeBound)
    (hlevel : ∀ (r : ℕ) {t : ℝ}, 0 < t → t < 1 →
      levelRate (r + 1) t < levelRate r t)
    (hclosure : ∀ r : ℕ, FixedLevelCompactifiedCertificateClosure r)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by sorry
