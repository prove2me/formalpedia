-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_sectionsEquiv_restrict
-- name    : GlobalTheory.Flasque.sectionsEquiv_restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:31:13.60653+00:00
-- url     : https://prove2.me/theorems/9411d9f5-c51a-4aa3-b1d1-f26f80a15063
-- title:
--   Flasque: sections Equiv restrict
-- statement:
--   The Flasque construction uses the sections Equiv restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L78-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

theorem GlobalTheory.Flasque.sectionsEquiv_restrict (F : Sheaf J AddCommGrpCat.{v}) {V U : C} (i : V ⟶ U)
    (x : F.H' 0 U) :
    sectionsEquiv F V ((F.cohomologyPresheaf 0).map i.op x) =
      F.obj.map i.op (sectionsEquiv F U x) := by sorry
