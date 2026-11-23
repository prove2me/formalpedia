-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_Inh_mem_stdLat
-- name    : GlobalTheory.PhiGam.Inh.mem_stdLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:27.80056+00:00
-- url     : https://prove2.me/theorems/30294e7f-da04-4792-b0d6-b6209ece7c48
-- title:
--   Inh: mem std Lat
-- statement:
--   The Inh construction uses the mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L365-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L365-L366

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

theorem GlobalTheory.PhiGam.Inh.mem_stdLat {x : k⸨X⸩} : x ∈ stdLat k ↔ ∃ a : k⟦X⟧, (a : k⸨X⸩) = x := by sorry
