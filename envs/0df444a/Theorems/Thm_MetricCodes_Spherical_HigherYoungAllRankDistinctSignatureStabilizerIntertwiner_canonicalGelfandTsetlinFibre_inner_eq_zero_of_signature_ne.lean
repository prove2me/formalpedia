-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankDistinctSignatureStabilizerIntertwiner_canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
-- name    : MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/60a5cf72-1846-4219-9a3f-c2750cdc2595
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
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
set_option maxRecDepth 4096
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAllRankActualHighestKernelRigidity
open MetricCodes.Spherical.HigherYoungAllRankStabilizerHighestCyclicity
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner.canonicalGelfandTsetlinFibre_inner_eq_zero_of_signature_ne
    {r n : ℕ} (hstable : 2 * (r + 1) + 2 ≤ n)
    (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hmu : Interlaces lam mu) (hnu : Interlaces lam nu)
    (hmuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam mu hmu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu)
    (hne : mu ≠ nu)
    (p : HarmonicYoungSpace (n := n) mu)
    (q : HarmonicYoungSpace (n := n) nu) :
    ⟪canonicalGelfandTsetlinFibre lam mu hmu hmuGram p,
      canonicalGelfandTsetlinFibre lam nu hnu hnuGram q⟫_ℝ = 0 := by sorry
