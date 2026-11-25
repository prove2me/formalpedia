-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_pull_le_pull
-- name    : GlobalTheory.PhiGam.pull_le_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:13.202457+00:00
-- url     : https://prove2.me/theorems/3bfdf771-acbc-59ef-a0eb-f61572598d17
-- title:
--   Phi Gam: pull le pull
-- statement:
--   The Phi Gam construction uses the pull le pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L153-L155

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
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
omit [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem GlobalTheory.PhiGam.pull_le_pull [Module k V] (f : V →ₗ[k] V) {N N' : Submodule k⟦X⟧ V} (h : N ≤ N') :
    pull f N ≤ pull f N' := by sorry
