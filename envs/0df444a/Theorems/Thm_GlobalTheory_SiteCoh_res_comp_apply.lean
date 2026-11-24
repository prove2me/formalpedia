-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_res_comp_apply
-- name    : GlobalTheory.SiteCoh.res_comp_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:22.373915+00:00
-- url     : https://prove2.me/theorems/936ba734-036e-4993-94eb-a209176e54fd
-- title:
--   Site Coh: res comp apply
-- statement:
--   The Site Coh construction uses the res comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L230-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L230-L232

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {F G H : Sheaf J AddCommGrpCat.{v}} {n : ℕ} {U V W : C}

theorem GlobalTheory.SiteCoh.res_comp_apply (i : V ⟶ U) (j : W ⟶ V) (x : F.H' n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by sorry
