-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseEigenNodeSeparation_positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation.positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:14.457341+00:00
-- url     : https://prove2.me/theorems/d4ace09d-989d-4e59-a510-d8bc7b2c84a0
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation.positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation.positiveStabilizerNode_ne_signedAmbientNode_of_valid_lower
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (row : Fin (r + 1))
    (hlower : mu = raiseWeight nu row)
    (hnu : Interlaces lam nu)
    (channel : Fin (r + 2) × Bool) :
    gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, true)) ≠
      signedNode (ambientShift (n + 1) lam) channel := by sorry
