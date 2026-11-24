-- Prove2me | Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_ll
-- name    : GlobalTheory.JR.UnitGLift.full_apply_ll
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:37:38.897397+00:00
-- url     : https://prove2.me/theorems/d15f9484-1586-44cb-98f2-309a20d6a6f2
-- title:
--   Unit GLift: full apply ll
-- statement:
--   The Unit GLift construction uses the full apply ll property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis.lean#L20-L21

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

theorem GlobalTheory.JR.UnitGLift.full_apply_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by sorry
