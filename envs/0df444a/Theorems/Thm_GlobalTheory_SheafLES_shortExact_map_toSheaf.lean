-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_shortExact_map_toSheaf
-- name    : GlobalTheory.SheafLES.shortExact_map_toSheaf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:16.09759+00:00
-- url     : https://prove2.me/theorems/fc4224d2-8be2-4296-b215-bafb901554c2
-- title:
--   Sheaf LES: short Exact map to Sheaf
-- statement:
--   The Sheaf LES construction uses the short Exact map to Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L307-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L307-L309

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
universe v' u'
variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem GlobalTheory.SheafLES.shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{v} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf.{v} R)).ShortExact := by sorry
