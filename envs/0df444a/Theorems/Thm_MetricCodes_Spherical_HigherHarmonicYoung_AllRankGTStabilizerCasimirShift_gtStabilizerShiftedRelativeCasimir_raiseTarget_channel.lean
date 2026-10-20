-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift.gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:10.573365+00:00
-- url     : https://prove2.me/theorems/99822174-07a2-4743-9e05-31c81fe10bd5
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift.gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
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
set_option maxHeartbeats 2500000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift.gtStabilizerShiftedRelativeCasimir_raiseTarget_channel
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (A : HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) (raiseWeight mu row)))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation mu a b) =
        (ClebschRotation.tensorAmbientRotation
          (raiseWeight mu row) a b).comp A)
    (p : HarmonicYoungSpace (n := n) mu) :
    gtStabilizerShiftedRelativeCasimir (raiseWeight mu row) (A p) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu) (.inr (row, false)) • A p := by sorry
