-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseAppendedChannelOrthogonality_appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality.appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:12.645026+00:00
-- url     : https://prove2.me/theorems/7122f105-b81e-42c6-8b95-8463b3c55e3a
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality.appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedClebschOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.CrossGram
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankDistinctSignatureStabilizerIntertwiner
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseAppendedChannelOrthogonality.appendedFullBranchPieriLower_adjoint_paddedPhysicalStabilizerTensor_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hmu : Antitone mu)
    (B : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hB : ∀ a b : Fin n,
      B.comp (youngAmbientRotation mu a b) =
        (tensorAmbientRotation lam a.castSucc b.castSucc).comp B)
    (hdominant : Antitone (appendZeroWeight lam))
    (hsource : Antitone
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2))))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (nu : FullBranchWeight
      (raiseWeight (appendZeroWeight lam) (Fin.last (r + 2)))) :
    (appendedFullBranchPieriLower
      lam hdominant hsource hn nu).adjoint.comp
        (paddedPhysicalStabilizerTensor lam mu B) = 0 := by sorry
