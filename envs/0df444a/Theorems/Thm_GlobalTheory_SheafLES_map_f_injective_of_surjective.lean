-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_f_injective_of_surjective
-- name    : GlobalTheory.SheafLES.map_f_injective_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:22.876639+00:00
-- url     : https://prove2.me/theorems/ebd09bec-b150-4fed-ba0a-50e5f9fa6e99
-- title:
--   Sheaf LES: map f injective of surjective
-- statement:
--   The Sheaf LES construction uses the map f injective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L231-L238

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

theorem GlobalTheory.SheafLES.map_f_injective_of_surjective (n : ℕ) (U : C)
    (h : Function.Surjective (map.{w'} S.g n U)) :
    Function.Injective (map.{w'} S.f (n + 1) U) := by sorry
