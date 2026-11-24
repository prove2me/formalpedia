-- Prove2me | Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_lc
-- name    : GlobalTheory.JR.UnitGLift.full_apply_lc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:49.325286+00:00
-- url     : https://prove2.me/theorems/a962af9c-a485-4b60-b77f-efaf222b95b7
-- title:
--   Unit GLift: full apply lc
-- statement:
--   The Unit GLift construction uses the full apply lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitGLift
variable {k : Type} [CommRing k] {r : ℕ}

theorem GlobalTheory.JR.UnitGLift.full_apply_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by sorry
