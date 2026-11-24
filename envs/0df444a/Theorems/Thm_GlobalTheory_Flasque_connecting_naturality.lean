-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_connecting_naturality
-- name    : GlobalTheory.Flasque.connecting_naturality
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:54.931897+00:00
-- url     : https://prove2.me/theorems/b4b24256-3b62-40b6-851c-97698692be9d
-- title:
--   Flasque: connecting naturality
-- statement:
--   The Flasque construction uses the connecting naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L115-L124

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

theorem GlobalTheory.Flasque.connecting_naturality {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) (U : C) (x : S.X₃.H' n U) :
    connecting hT n U (((Sheaf.cohomologyPresheafFunctor J n).map φ.τ₃).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor J (n + 1)).map φ.τ₁).app (op U) (connecting hS n U x) := by sorry
