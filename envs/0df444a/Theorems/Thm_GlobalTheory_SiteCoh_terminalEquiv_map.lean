-- Prove2me | Theorems.Thm_GlobalTheory_SiteCoh_terminalEquiv_map
-- name    : GlobalTheory.SiteCoh.terminalEquiv_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:31.033869+00:00
-- url     : https://prove2.me/theorems/41783c81-aa96-47af-a935-c7ed4fbf5ad7
-- title:
--   Site Coh: terminal Equiv map
-- statement:
--   The Site Coh construction uses the terminal Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/SubsingletonOfSubsingletonFreeSheaf.lean#L143-L149

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

theorem GlobalTheory.SiteCoh.terminalEquiv_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by sorry
