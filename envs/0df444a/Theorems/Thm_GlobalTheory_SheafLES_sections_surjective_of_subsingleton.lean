-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_sections_surjective_of_subsingleton
-- name    : GlobalTheory.SheafLES.sections_surjective_of_subsingleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:26.794797+00:00
-- url     : https://prove2.me/theorems/161e3bc2-5b18-4aee-96f6-4cd0218b5c3f
-- title:
--   Sheaf LES: sections surjective of subsingleton
-- statement:
--   The Sheaf LES construction uses the sections surjective of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L216-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L216-L218

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

theorem GlobalTheory.SheafLES.sections_surjective_of_subsingleton (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U)) : Function.Surjective (S.g.hom.app (op U)) := by sorry
