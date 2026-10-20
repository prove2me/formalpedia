-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTValidTransverseSectorFamily_normalizedNegativeSector_canonicalAxis_inner_eq_zero
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily.normalizedNegativeSector_canonicalAxis_inner_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/08f0d4ac-b48e-4883-9c5b-62fbdd6808fc
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily.normalizedNegativeSector_canonicalAxis_inner_eq_zero
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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSignedIndex
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily.normalizedNegativeSector_canonicalAxis_inner_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (kappa : Fin r → ℕ)
    (hmu : Interlaces lam mu)
    (hmuGram : PositiveGelfandTsetlinFischerGram (n := n) lam mu hmu)
    (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (hfinite : FiniteInterlacing n mu kappa)
    (hraise : FiniteInterlacing n (raiseWeight mu row) kappa)
    (p q : HarmonicYoungSpace (n := n) mu) :
    ⟪canonicalGelfandTsetlinAxisTensor lam mu hmu hmuGram p,
      normalizedGTTransverseNegativeSector
        lam mu kappa row hnu hnuGram hfinite hraise q⟫_ℝ = 0 := by sorry
