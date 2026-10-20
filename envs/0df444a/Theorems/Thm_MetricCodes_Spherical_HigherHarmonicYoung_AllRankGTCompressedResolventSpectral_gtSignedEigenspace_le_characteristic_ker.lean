-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCompressedResolventSpectral_gtSignedEigenspace_le_characteristic_ker
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral.gtSignedEigenspace_le_characteristic_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/459283df-df0a-448e-acfe-e3e8c966356b
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral.gtSignedEigenspace_le_characteristic_ker
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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAppendedRowExclusion
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral.gtSignedEigenspace_le_characteristic_ker {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (z : Fin (r + 1) × Bool) :
    Module.End.eigenspace (gtRelativeCasimir (n := n) lam)
        (signedNode (HigherChannel.ambientShift n lam) z) ≤
      LinearMap.ker
        (Polynomial.aeval (gtRelativeCasimir (n := n) lam)
          (gtChannelCharacteristicPolynomial n lam)) := by sorry
