-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_comp
-- name    : GlobalTheory.SheafLES.map_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:40.19431+00:00
-- url     : https://prove2.me/theorems/f8b099d7-2750-44a1-b5d6-0bbae229aa79
-- title:
--   Sheaf LES: map comp
-- statement:
--   The Sheaf LES construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L85-L89

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

theorem GlobalTheory.SheafLES.map_comp (f : F ⟶ G) (g : G ⟶ K) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by sorry
