-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_equivZero_map
-- name    : GlobalTheory.SheafLES.equivZero_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:17.201174+00:00
-- url     : https://prove2.me/theorems/db4a8769-ff4a-4da0-ae90-026ae2bc7b30
-- title:
--   Sheaf LES: equiv Zero map
-- statement:
--   The Sheaf LES construction uses the equiv Zero map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L128-L131

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

theorem GlobalTheory.SheafLES.equivZero_map (f : F ⟶ G) (U : C) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero G U (map f 0 U x) = f.hom.app (op U) (equivZero F U x) := by sorry
