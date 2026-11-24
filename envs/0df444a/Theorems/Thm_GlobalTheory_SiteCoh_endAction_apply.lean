-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_endAction_apply
-- name    : GlobalTheory.SiteCoh.endAction_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:38.348849+00:00
-- url     : https://prove2.me/theorems/c2758e33-1edc-4d79-9764-d8570510d474
-- title:
--   Site Coh: end Action apply
-- statement:
--   The Site Coh construction uses the end Action apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L248-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ToAbSheafPreservesFiniteLimits.lean#L248-L248

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

theorem GlobalTheory.SiteCoh.endAction_apply (f : End F) (x : F.H' n U) : endAction F n U f x = map f n U x := by sorry
