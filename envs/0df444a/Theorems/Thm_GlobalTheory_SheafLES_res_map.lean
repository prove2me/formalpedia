-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_res_map
-- name    : GlobalTheory.SheafLES.res_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:41.991144+00:00
-- url     : https://prove2.me/theorems/aa527c45-4119-4d03-b7ee-6befff7b336d
-- title:
--   Sheaf LES: res map
-- statement:
--   The Sheaf LES construction uses the res map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L112-L115

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

theorem GlobalTheory.SheafLES.res_map (f : F ⟶ G) (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F n U) :
    res G n i (map f n U x) = map f n V (res F n i x) := by sorry
