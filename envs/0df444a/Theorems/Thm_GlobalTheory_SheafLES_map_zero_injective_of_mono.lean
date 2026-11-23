-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_map_zero_injective_of_mono
-- name    : GlobalTheory.SheafLES.map_zero_injective_of_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:26.198366+00:00
-- url     : https://prove2.me/theorems/68c11f83-8f25-4625-aea7-b36ff34de93a
-- title:
--   Sheaf LES: map zero injective of mono
-- statement:
--   The Sheaf LES construction uses the map zero injective of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L169-L171

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

theorem GlobalTheory.SheafLES.map_zero_injective_of_mono {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f]
    (U : C) : Function.Injective (map.{w'} f 0 U) := by sorry
