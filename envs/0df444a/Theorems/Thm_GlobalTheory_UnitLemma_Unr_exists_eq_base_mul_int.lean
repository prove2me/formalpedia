-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_exists_eq_base_mul_int
-- name    : GlobalTheory.UnitLemma.Unr.exists_eq_base_mul_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:53.483246+00:00
-- url     : https://prove2.me/theorems/7e33697c-b94c-4711-bdf2-4f41cba79063
-- title:
--   Unr: exists eq base mul int
-- statement:
--   The Unr construction uses the exists eq base mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIff.lean#L96-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeOverUnramifiedExtIff.lean#L96-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.Unr.exists_eq_base_mul_int {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E) :
    ∃ (e : K.E) (b : K'.O), z = φ e * algebraMap K'.O K'.E b := by sorry
