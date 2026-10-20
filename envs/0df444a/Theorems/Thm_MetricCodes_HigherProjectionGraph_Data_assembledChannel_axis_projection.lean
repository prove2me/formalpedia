-- Prove2me | Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_assembledChannel_axis_projection
-- name    : MetricCodes.HigherProjectionGraph.Data.assembledChannel_axis_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/7eb565fd-5519-4bbd-903d-80cfe941e996
-- title:
--   MetricCodes.HigherProjectionGraph.Data.assembledChannel_axis_projection
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
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open MetricCodes.HigherProjectionGraph
variable {I X : Type*} [Fintype I] [DecidableEq I]
open MetricCodes.HigherProjectionGraph.Data
variable {D d Q : ℕ} (A : Data I X D d Q)

theorem MetricCodes.HigherProjectionGraph.Data.assembledChannel_axis_projection [Nonempty I] (x : X) :
    (A.assembledChannel)ᵀ * A.axis x * A.combinedProjection x =
      Real.sqrt A.eigenvalue • A.combinedProjection x := by sorry
