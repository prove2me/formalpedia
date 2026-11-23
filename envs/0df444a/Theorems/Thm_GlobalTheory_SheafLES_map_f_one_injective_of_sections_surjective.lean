-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_f_one_injective_of_sections_surjective
-- name    : GlobalTheory.SheafLES.map_f_one_injective_of_sections_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:25.252664+00:00
-- url     : https://prove2.me/theorems/a12451b5-4f02-4140-a7bc-931708331cca
-- title:
--   Sheaf LES: map f one injective of sections surjective
-- statement:
--   The Sheaf LES construction uses the map f one injective of sections surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L240-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L240-L245

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
include hS

theorem GlobalTheory.SheafLES.map_f_one_injective_of_sections_surjective (U : C)
    (h : Function.Surjective (S.g.hom.app (op U))) : Function.Injective (map.{w'} S.f 1 U) := by sorry
