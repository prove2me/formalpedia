-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram_canonicalBranchProjectedLower_orthogonal_of_ne_selected
-- name    : MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLower_orthogonal_of_ne_selected
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/a22b59b0-8e94-4f4e-9ebe-1ff7aceccafc
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLower_orthogonal_of_ne_selected
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
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram.canonicalBranchProjectedLower_orthogonal_of_ne_selected
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (hlow : Interlaces low mu) (hhigh : Interlaces high mu)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (nu : FullBranchWeight low)
    (hne : nu ≠ fullBranchOfInterlaces mu hlow)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) (fullBranchSignature nu)) :
    ⟪projectedCoordinateLower low high hdeg row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (canonicalGelfandTsetlinFibre high mu hhigh
          (positiveGelfandTsetlinFischerGram (r := r) (n := n) (by omega)
            high mu hhigh) p),
      canonicalFullBranchFibre low hn nu q⟫_ℝ = 0 := by sorry
