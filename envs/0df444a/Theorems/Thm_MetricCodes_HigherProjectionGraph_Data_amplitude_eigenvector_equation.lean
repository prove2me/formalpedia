-- Prove2me | Theorems.Thm_MetricCodes_HigherProjectionGraph_Data_amplitude_eigenvector_equation
-- name    : MetricCodes.HigherProjectionGraph.Data.amplitude_eigenvector_equation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/0e4a87ff-bb93-4bc4-99a5-3171d332b055
-- title:
--   MetricCodes.HigherProjectionGraph.Data.amplitude_eigenvector_equation
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

theorem MetricCodes.HigherProjectionGraph.Data.amplitude_eigenvector_equation [Nonempty I] (source : I) :
    (∑ target,
      A.probability target source * A.amplitude target ^ 2) =
      A.eigenvalue * A.amplitude source ^ 2 := by sorry
