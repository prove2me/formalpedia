-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_res_comp
-- name    : GlobalTheory.SheafLES.res_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:39.833188+00:00
-- url     : https://prove2.me/theorems/aa1bb483-b0b6-4987-ba36-923374e7703f
-- title:
--   Sheaf LES: res comp
-- statement:
--   The Sheaf LES construction uses the res comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L108-L110

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

theorem GlobalTheory.SheafLES.res_comp (n : ℕ) {U V W : C} (i : V ⟶ U) (j : W ⟶ V) (x : Sheaf.H'.{w'} F n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by sorry
