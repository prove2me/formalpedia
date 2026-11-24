-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_pull_stdLat
-- name    : GlobalTheory.PhiGam.Inh.pull_stdLat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:44:50.730038+00:00
-- url     : https://prove2.me/theorems/8a5acf53-ffc3-433a-884c-a5fa45e65c50
-- title:
--   Inh: pull std Lat
-- statement:
--   The Inh construction uses the pull std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L374-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L374-L383

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

theorem GlobalTheory.PhiGam.Inh.pull_stdLat {l : ℕ} (R : RingPG k l) : pull (lin R.φ) (stdLat k) = stdLat k := by sorry
