-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_res_apply
-- name    : GlobalTheory.SheafLES.res_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:48.290486+00:00
-- url     : https://prove2.me/theorems/58358ad5-4d1a-4217-95fc-f932dfb14684
-- title:
--   Sheaf LES: res apply
-- statement:
--   The Sheaf LES construction uses the res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L79-L80

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

theorem GlobalTheory.SheafLES.res_apply (n : ℕ) {U V : C} (i : V ⟶ U) (x : Ext.{w'} ((freeYoneda J).obj U) F n) :
    res F n i x = (Ext.mk₀ ((freeYoneda J).map i)).comp x (zero_add n) := by sorry
