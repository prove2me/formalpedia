-- Prove2me | Theorems.Thm_GlobalTheory_SheafLES_freeYonedaHomEquiv_map_comp
-- name    : GlobalTheory.SheafLES.freeYonedaHomEquiv_map_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:38.587319+00:00
-- url     : https://prove2.me/theorems/e4d1983c-9ea9-4b37-bb83-9d5ff9af404a
-- title:
--   Sheaf LES: free Yoneda Hom Equiv map comp
-- statement:
--   The Sheaf LES construction uses the free Yoneda Hom Equiv map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L40-L53

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

theorem GlobalTheory.SheafLES.freeYonedaHomEquiv_map_comp {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) :
    freeYonedaHomEquiv V F ((freeYoneda J).map i ≫ φ) =
      F.obj.map i.op (freeYonedaHomEquiv U F φ) := by sorry
