-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBoxReverseRange_canonicalBoxReverseAxisRange_of_strongStable
-- name    : MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange.canonicalBoxReverseAxisRange_of_strongStable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/3839cc06-7360-4041-8758-9cc01ad65849
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange.canonicalBoxReverseAxisRange_of_strongStable
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
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBranchProjectedLowerCrossGram
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness

theorem MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange.canonicalBoxReverseAxisRange_of_strongStable
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row) :
    CanonicalBoxReverseAxisRange
      a b hstable hgram low high row hrow := by sorry
