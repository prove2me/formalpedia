-- Prove2me | Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_lift_transpose_mul_lift
-- name    : MetricCodes.HigherProjectionGraph.Data.lift_transpose_mul_lift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/df1cb374-8559-4a82-8494-16b231f8f1e2
-- title:
--   MetricCodes.HigherProjectionGraph.Data.lift_transpose_mul_lift
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

theorem MetricCodes.HigherProjectionGraph.Data.lift_transpose_mul_lift [Nonempty I] (x y : X) :
    (A.lift x)ᵀ * A.lift y =
      A.correlation x y •
        (A.combinedProjection x * A.combinedProjection y) := by sorry
