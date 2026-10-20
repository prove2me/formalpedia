-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAxisCompressedCharacteristicMinor_gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor.gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/9545e384-15dd-4532-bd98-3e1d665d5438
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor.gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
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
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor.gtAxisCompressedSignedProjectorCoefficient_pos_eq_plusProbability_of_minor
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu)
    (hminor : gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      Polynomial.C ⟪p, q⟫_ℝ *
        channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
          (stabilizerShift (n + 1) mu))
    (row : Fin (r + 2)) :
    gtAxisCompressedSignedProjectorCoefficient
        lam mu h hgram p q (row, true) =
      ⟪p, q⟫_ℝ * plusProbability (n + 1) lam mu row := by sorry
