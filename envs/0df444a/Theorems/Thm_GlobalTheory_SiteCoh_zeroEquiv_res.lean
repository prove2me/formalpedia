-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_res
-- name    : GlobalTheory.SiteCoh.zeroEquiv_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:30.545048+00:00
-- url     : https://prove2.me/theorems/4d2641f7-9195-49cd-88d6-5d485d250f77
-- title:
--   Site Coh: zero Equiv res
-- statement:
--   The Site Coh construction uses the zero Equiv res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L124-L131

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

theorem GlobalTheory.SiteCoh.zeroEquiv_res (F : Sheaf J AddCommGrpCat.{v}) {U V : C} (i : V ⟶ U) (x : F.H' 0 U) :
    zeroEquiv F V (res F 0 i x) = F.obj.map i.op (zeroEquiv F U x) := by sorry
