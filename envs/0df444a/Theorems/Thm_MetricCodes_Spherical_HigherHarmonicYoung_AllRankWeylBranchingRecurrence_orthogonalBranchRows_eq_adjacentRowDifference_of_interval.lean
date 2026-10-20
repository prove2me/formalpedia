-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankWeylBranchingRecurrence_orthogonalBranchRows_eq_adjacentRowDifference_of_interval
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.orthogonalBranchRows_eq_adjacentRowDifference_of_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/69cca51c-0331-4e1e-a623-e05a13fddfbc
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.orthogonalBranchRows_eq_adjacentRowDifference_of_interval
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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHierarchy

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.orthogonalBranchRows_eq_adjacentRowDifference_of_interval
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (hinterval : ∀ (L U : ℕ), L ≤ U → ∀ shift : ℤ,
      (∑ a : {k : Fin (U + 1) // L ≤ k.val},
        orthogonalCompleteSymmetricCoefficient (n - 1)
          ((a.val.val : ℤ) + shift)) =
        orthogonalCompleteSymmetricCoefficient n
            ((U : ℤ) + shift) -
          orthogonalCompleteSymmetricCoefficient n
            (((L : ℤ) - 1) + shift)) :
    (fun i j =>
      ∑ a : OrthogonalBranchCoordinate lam i,
        orthogonalBranchRow n lam i a j) =
      adjacentRowDifference (orthogonalJacobiTrudiMatrix n lam) := by sorry
