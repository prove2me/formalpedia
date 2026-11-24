-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_freeSheafHomEquiv_map_comp
-- name    : GlobalTheory.SiteCoh.freeSheafHomEquiv_map_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:13:33.935813+00:00
-- url     : https://prove2.me/theorems/fde9c23a-4cca-4807-9f75-5c4f3725fad4
-- title:
--   Site Coh: free Sheaf Hom Equiv map comp
-- statement:
--   The Site Coh construction uses the free Sheaf Hom Equiv map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L48-L54

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

theorem GlobalTheory.SiteCoh.freeSheafHomEquiv_map_comp {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) :
    freeSheafHomEquiv V F ((freeSheaf J).map i ≫ φ) =
      F.obj.map i.op (freeSheafHomEquiv U F φ) := by sorry
