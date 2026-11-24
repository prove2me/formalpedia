-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_freeSheafHomEquiv_freeSheafMap_comp
-- name    : GlobalTheory.Flasque.freeSheafHomEquiv_freeSheafMap_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:31:30.15255+00:00
-- url     : https://prove2.me/theorems/98360f10-6b0e-45a7-80e7-f28ff310afc3
-- title:
--   Flasque: free Sheaf Hom Equiv free Sheaf Map comp
-- statement:
--   The Flasque construction uses the free Sheaf Hom Equiv free Sheaf Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L55-L59

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

theorem GlobalTheory.Flasque.freeSheafHomEquiv_freeSheafMap_comp {V U : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (f : freeSheaf J U ⟶ F) :
    freeSheafHomEquiv V F (freeSheafMap J i ≫ f) = F.obj.map i.op (freeSheafHomEquiv U F f) := by sorry
