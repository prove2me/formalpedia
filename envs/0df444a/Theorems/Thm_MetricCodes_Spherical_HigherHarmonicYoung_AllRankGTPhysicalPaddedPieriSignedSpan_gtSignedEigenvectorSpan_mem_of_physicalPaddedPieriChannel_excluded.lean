-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalPaddedPieriSignedSpan_gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan.gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:09.321996+00:00
-- url     : https://prove2.me/theorems/059bb34b-7a7e-4585-bd7b-21e7a393dcec
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan.gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirZeroRowTransport
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalPaddedPieriSignedSpan.gtSignedEigenvectorSpan_mem_of_physicalPaddedPieriChannel_excluded
    {r n : ℕ} (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hexcluded :
      ∀ i : PaddedPieriChannel (appendZeroWeight lam),
        ¬ retainedPaddedPieriChannel lam i →
          ∀ q : HarmonicYoungSpace (n := n)
            (paddedPieriSource (appendZeroWeight lam) i),
              ⟪v, physicalPaddedPieriChannel hn lam hdom i q⟫_ℝ = 0) :
    v ∈ gtSignedEigenvectorSpan (n := n) lam := by sorry
