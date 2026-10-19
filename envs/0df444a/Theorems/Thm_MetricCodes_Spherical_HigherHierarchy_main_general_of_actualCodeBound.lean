-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_main_general_of_actualCodeBound
-- name    : MetricCodes.Spherical.HigherHierarchy.main_general_of_actualCodeBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:52.737619+00:00
-- url     : https://prove2.me/theorems/8bdc0ce2-c599-46f0-a924-df33fefc48b1
-- title:
--   MetricCodes.Spherical.HigherHierarchy.main_general_of_actualCodeBound
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
open Filter Topology
open scoped Topology

theorem MetricCodes.Spherical.HigherHierarchy.main_general_of_actualCodeBound
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by sorry
