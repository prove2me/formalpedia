-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransportedPieriOrthogonality_physicalPaddedPieriChannel_inner_eq_zero
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality.physicalPaddedPieriChannel_inner_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:09.321996+00:00
-- url     : https://prove2.me/theorems/40e63e28-868f-4497-8720-603ec788c03c
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality.physicalPaddedPieriChannel_inner_eq_zero
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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransportedPieriOrthogonality.physicalPaddedPieriChannel_inner_eq_zero {r n : ℕ}
    (hn : 2 * (r + 1) + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ)
    (hdom : Antitone (appendZeroWeight lam))
    (i j : PaddedPieriChannel (appendZeroWeight lam)) (hij : i ≠ j)
    (p : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) i))
    (q : HarmonicYoungSpace (n := n)
      (paddedPieriSource (appendZeroWeight lam) j)) :
    ⟪physicalPaddedPieriChannel hn lam hdom i p,
      physicalPaddedPieriChannel hn lam hdom j q⟫_ℝ = 0 := by sorry
