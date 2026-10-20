-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape
-- name    : MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:52.737619+00:00
-- url     : https://prove2.me/theorems/09463344-ad14-4f39-84b5-fb7935b20c07
-- title:
--   MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape
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
open scoped Topology

theorem MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc_of_jointEscape
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hescape : ∀ {u a : ℕ → ℝ} {t : ℝ}, 0 < t → t < 1 →
      Tendsto u atTop (nhds t) → Tendsto a atTop atTop →
      Tendsto (fun n => oneRowBoundaryObjective (u n) (a n))
        atTop (nhds (-(1 / 2 : ℝ) * Real.logb 2 (1 - t)))) :
    LowerSemicontinuousOn MetricCodes.Spherical.variationalRate
      (Set.Icc (0 : ℝ) s) := by sorry
