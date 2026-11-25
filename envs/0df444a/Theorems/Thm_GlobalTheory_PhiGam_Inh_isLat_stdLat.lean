-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_isLat_stdLat
-- name    : GlobalTheory.PhiGam.Inh.isLat_stdLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:06.346806+00:00
-- url     : https://prove2.me/theorems/4f99ae2a-041a-590c-9ce0-a5f92f198b1b
-- title:
--   Inh: is Lat std Lat
-- statement:
--   The Inh construction uses the is Lat std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L368-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L368-L372

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

theorem GlobalTheory.PhiGam.Inh.isLat_stdLat : IsLat (stdLat k) := by sorry
