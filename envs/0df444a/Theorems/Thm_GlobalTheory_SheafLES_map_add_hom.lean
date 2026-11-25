-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_add_hom
-- name    : GlobalTheory.SheafLES.map_add_hom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:43.343416+00:00
-- url     : https://prove2.me/theorems/878b319c-bc6d-4875-a885-004e46ab2b6a
-- title:
--   Sheaf LES: map add hom
-- statement:
--   The Sheaf LES construction uses the map add hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L97-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}

theorem GlobalTheory.SheafLES.map_add_hom (f g : F ⟶ G) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f + g) n U x = map f n U x + map g n U x := by sorry
