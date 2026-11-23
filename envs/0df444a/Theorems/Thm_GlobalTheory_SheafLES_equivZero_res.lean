-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_equivZero_res
-- name    : GlobalTheory.SheafLES.equivZero_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:29.539083+00:00
-- url     : https://prove2.me/theorems/4880de73-7c26-47ad-9748-dae893740aa8
-- title:
--   Sheaf LES: equiv Zero res
-- statement:
--   The Sheaf LES construction uses the equiv Zero res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L133-L136

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

theorem GlobalTheory.SheafLES.equivZero_res {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero F V (res F 0 i x) = F.obj.map i.op (equivZero F U x) := by sorry
