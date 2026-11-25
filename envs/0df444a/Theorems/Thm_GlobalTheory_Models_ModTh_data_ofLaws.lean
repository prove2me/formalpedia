-- Prove2me | Theorems.Thm_GlobalTheory_Models_ModTh_data_ofLaws
-- name    : GlobalTheory.Models.ModTh.data_ofLaws
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:09.624313+00:00
-- url     : https://prove2.me/theorems/1cc2e6f0-9f41-52a4-972f-62ea2998eac8
-- title:
--   Mod Th: data of Laws
-- statement:
--   The Mod Th construction uses the data of Laws property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L361-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L361-L362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}

theorem GlobalTheory.Models.ModTh.data_ofLaws {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (Y : ModData k G n) (h : Law.All F Dt Y) :
    (ModTh.ofLaws Y h).data = Y := by sorry
