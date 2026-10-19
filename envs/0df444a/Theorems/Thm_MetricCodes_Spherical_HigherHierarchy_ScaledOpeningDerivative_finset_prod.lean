-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ScaledOpeningDerivative_finset_prod
-- name    : MetricCodes.Spherical.HigherHierarchy.ScaledOpeningDerivative.finset_prod
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:40.58935+00:00
-- url     : https://prove2.me/theorems/1844b179-4dc9-4ff7-970c-f61075a0b867
-- title:
--   MetricCodes.Spherical.HigherHierarchy.ScaledOpeningDerivative.finset_prod
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
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.ScaledOpeningDerivative.finset_prod {ι : Type*} {η : ℝ}
    (s : Finset ι) {f F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ScaledOpeningDerivative η (f i) (F i)) :
    ScaledOpeningDerivative η
      (fun t => ∏ i ∈ s, f i t)
      (fun t => ∏ i ∈ s, F i t) := by sorry
