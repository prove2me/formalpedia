-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalGelfandTsetlinCompleteness_canonicalFullBranch_finrank_sum
-- name    : MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranch_finrank_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/aa7637d6-7eab-4c85-9297-e312fd17e8f5
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranch_finrank_sum
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
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualBranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness.canonicalFullBranch_finrank_sum {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (hn : 2 * r + 5 ≤ n)
    (hdom : Antitone lam) (hbranch : WeylBranchingRecurrence n lam) :
    Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) =
      ∑ mu : FullBranchWeight lam,
        Module.finrank ℝ
          (HarmonicYoungSpace (n := n - 1) (fullBranchSignature mu)) := by sorry
