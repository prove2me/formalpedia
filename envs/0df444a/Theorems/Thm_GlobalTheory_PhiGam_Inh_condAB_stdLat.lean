-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_condAB_stdLat
-- name    : GlobalTheory.PhiGam.Inh.condAB_stdLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:20.823808+00:00
-- url     : https://prove2.me/theorems/6ee5226b-0ffd-4638-a97a-2c622555b55c
-- title:
--   Inh: cond AB std Lat
-- statement:
--   The Inh construction uses the cond AB std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L385-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L385-L389

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

theorem GlobalTheory.PhiGam.Inh.condAB_stdLat {l : ℕ} (R : RingPG k l) (hγ : Function.Bijective R.γ) (n : ℕ) :
    CondAB (unitMod R hγ n).φ (fun _ => 0) (fun _ => 0) (fun _ => stdLat k) := by sorry
