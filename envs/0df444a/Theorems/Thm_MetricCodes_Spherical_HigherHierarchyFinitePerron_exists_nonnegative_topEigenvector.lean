-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_nonnegative_topEigenvector
-- name    : MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_nonnegative_topEigenvector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/dbe77fb1-0133-497a-ad03-2cca74e94ca8
-- title:
--   MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_nonnegative_topEigenvector
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
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem MetricCodes.Spherical.HigherHierarchyFinitePerron.exists_nonnegative_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hnonneg : ∀ i j : I, 0 ≤ A i j) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 ≤ x i := by sorry
