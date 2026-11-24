-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_extEquiv_res
-- name    : GlobalTheory.SiteCoh.extEquiv_res
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:13:44.589803+00:00
-- url     : https://prove2.me/theorems/04edd801-1cb5-4cc1-aa01-f34e4b084369
-- title:
--   Site Coh: ext Equiv res
-- statement:
--   The Site Coh construction uses the ext Equiv res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L91-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

theorem GlobalTheory.SiteCoh.extEquiv_res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U)
    (x : F.H' n U) :
    extEquiv F n V (res F n i x) =
      (Ext.mk₀ ((freeSheaf J).map i)).comp (extEquiv F n U x) (zero_add n) := by sorry
