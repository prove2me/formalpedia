-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_apply
-- name    : GlobalTheory.SheafLES.map_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:39.689908+00:00
-- url     : https://prove2.me/theorems/d4cd04c8-40d4-42df-aa1e-3d8aa444bc76
-- title:
--   Sheaf LES: map apply
-- statement:
--   The Sheaf LES construction uses the map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L76-L77

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

theorem GlobalTheory.SheafLES.map_apply (f : F ⟶ G) (n : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda J).obj U) F n) :
    map f n U x = x.comp (Ext.mk₀ f) (add_zero n) := by sorry
