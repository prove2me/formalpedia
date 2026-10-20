-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCanonicalAxisSignedCharacteristic_gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
-- name    : MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic.gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/02acfd12-8757-4f97-ad33-f35b8b7b15ca
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic.gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherYoungAllRankGTCanonicalAxisSignedCharacteristic.gtChannelCharacteristic_aeval_canonicalAxis_eq_zero
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (p : HarmonicYoungSpace (n := n) mu) :
    Polynomial.aeval (gtRelativeCasimir (n := n + 1) lam)
        (gtChannelCharacteristicPolynomial (n + 1) lam)
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram p) = 0 := by sorry
