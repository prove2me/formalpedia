-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_connecting_restrict
-- name    : GlobalTheory.Flasque.connecting_restrict
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:31:41.170565+00:00
-- url     : https://prove2.me/theorems/2eb4dd7c-3869-4db3-aead-ef28905b8d22
-- title:
--   Flasque: connecting restrict
-- statement:
--   The Flasque construction uses the connecting restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L126-L129

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

theorem GlobalTheory.Flasque.connecting_restrict (n : ℕ) {V U : C} (i : V ⟶ U) (x : S.X₃.H' n U) :
    connecting hS n V ((S.X₃.cohomologyPresheaf n).map i.op x) =
      (S.X₁.cohomologyPresheaf (n + 1)).map i.op (connecting hS n U x) := by sorry
