-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_equivZero_symm
-- name    : GlobalTheory.SheafLES.map_equivZero_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:51.150794+00:00
-- url     : https://prove2.me/theorems/20f4c840-58ad-4e92-bc4b-33cbe7ac0b41
-- title:
--   Sheaf LES: map equiv Zero symm
-- statement:
--   The Sheaf LES construction uses the map equiv Zero symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L138-L141

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

theorem GlobalTheory.SheafLES.map_equivZero_symm (f : F ⟶ G) (U : C) (s : F.obj.obj (op U)) :
    map f 0 U ((equivZero.{w'} F U).symm s) = (equivZero G U).symm (f.hom.app (op U) s) := by sorry
