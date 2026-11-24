-- Prove2me | Theorems.Thm_GlobalTheory_Models_IsModel_le_maxModel
-- name    : GlobalTheory.Models.IsModel.le_maxModel
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:52.637621+00:00
-- url     : https://prove2.me/theorems/4ae89957-c3b6-4d06-9c49-6a0102091dcc
-- title:
--   Is Model: le max Model
-- statement:
--   The Is Model construction uses the le max Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L271-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L271-L273

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

theorem GlobalTheory.Models.IsModel.le_maxModel {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A : Ob k G}
    {N : Lats k n A.m} (h : IsModel F Base A N) (i : ZMod n) : N i ≤ maxModel F Base A i := by sorry
