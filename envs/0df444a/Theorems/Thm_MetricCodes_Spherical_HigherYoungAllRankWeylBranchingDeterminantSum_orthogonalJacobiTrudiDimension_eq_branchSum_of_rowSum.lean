-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingDeterminantSum_orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
-- name    : MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/79b7247c-ba0d-4b66-86f6-0724fc6cf5dd
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
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
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference

theorem MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.orthogonalJacobiTrudiDimension_eq_branchSum_of_rowSum
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hrow : ∀ (i j : Fin (r + 1)),
      (∑ x : {a : Fin (lam i + 1) // branchLower lam i ≤ a.val},
        branchJacobiTrudiRow (n - 1) lam i x j) =
        adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) i j) :
    orthogonalJacobiTrudiDimension n lam =
      ∑ mu : FullBranchWeight lam,
        orthogonalJacobiTrudiDimension (n - 1)
          (fullBranchSignature mu) := by sorry
