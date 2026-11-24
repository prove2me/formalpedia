-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_freeSheafMap_gen
-- name    : GlobalTheory.Flasque.freeSheafMap_gen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:52.726836+00:00
-- url     : https://prove2.me/theorems/1a23ac8b-38ed-4578-8b9e-4486377571eb
-- title:
--   Flasque: free Sheaf Map gen
-- statement:
--   The Flasque construction uses the free Sheaf Map gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L43-L53

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

theorem GlobalTheory.Flasque.freeSheafMap_gen {V U : C} (i : V ⟶ U) :
    (freeSheafMap J i).hom.app (op V) (freeSheafGen J V) =
      (freeSheaf J U).obj.map i.op (freeSheafGen J U) := by sorry
