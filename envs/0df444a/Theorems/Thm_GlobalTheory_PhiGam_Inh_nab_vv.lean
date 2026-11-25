-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_nab_vv
-- name    : GlobalTheory.PhiGam.Inh.nab_vv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:08.118333+00:00
-- url     : https://prove2.me/theorems/c6f77310-78c3-43aa-a1ac-e15827d7557e
-- title:
--   Inh: nab vv
-- statement:
--   The Inh construction uses the nab vv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L405-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L405-L412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam.Inh
variable {k : Type} [Field k]

theorem GlobalTheory.PhiGam.Inh.nab_vv {l : ℕ} (R : RingPG k l) :
    ∃ κ : k⟦X⟧, PowerSeries.constantCoeff κ = 1 ∧ nab (lin R.γ) (vv k) = -((κ : k⸨X⸩) * vv k) := by sorry
