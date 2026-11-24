-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_freeSheaf_map_tautSection
-- name    : GlobalTheory.SiteCoh.freeSheaf_map_tautSection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:52.966863+00:00
-- url     : https://prove2.me/theorems/c03882bf-6a38-4a13-87b0-846cc8f6483a
-- title:
--   Site Coh: free Sheaf map taut Section
-- statement:
--   The Site Coh construction uses the free Sheaf map taut Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L32-L46

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

theorem GlobalTheory.SiteCoh.freeSheaf_map_tautSection {U V : C} (i : V ⟶ U) :
    ((freeSheaf J).map i).hom.app (op V) (tautSection J V) =
      ((freeSheaf J).obj U).obj.map i.op (tautSection J U) := by sorry
