-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_nab_mem_stdLat
-- name    : GlobalTheory.PhiGam.Inh.nab_mem_stdLat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:00.340287+00:00
-- url     : https://prove2.me/theorems/e318e180-d1ad-4386-86b4-648d34e7d247
-- title:
--   Inh: nab mem std Lat
-- statement:
--   The Inh construction uses the nab mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L414-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L414-L429

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

theorem GlobalTheory.PhiGam.Inh.nab_mem_stdLat {l : ℕ} (R : RingPG k l) {x : k⸨X⸩} (hx : x ∈ stdLat k) :
    nab (lin R.γ) x ∈ sh 1 (stdLat k) := by sorry
