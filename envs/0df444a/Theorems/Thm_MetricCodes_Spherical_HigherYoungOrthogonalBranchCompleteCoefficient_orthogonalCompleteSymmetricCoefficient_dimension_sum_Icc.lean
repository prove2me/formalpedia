-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungOrthogonalBranchCompleteCoefficient_orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
-- name    : MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/518d1c73-5b63-40da-9dc2-8eed123f1f45
-- title:
--   MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant

theorem MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient.orthogonalCompleteSymmetricCoefficient_dimension_sum_Icc
    {n : ℕ} (hn : 2 ≤ n) {L U : ℕ} (hLU : L ≤ U) (shift : ℤ) :
    (∑ k ∈ Finset.Icc L U,
      orthogonalCompleteSymmetricCoefficient (n - 1) ((k : ℤ) + shift)) =
      orthogonalCompleteSymmetricCoefficient n ((U : ℤ) + shift) -
        orthogonalCompleteSymmetricCoefficient n (((L : ℤ) - 1) + shift) := by sorry
