-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_pull_pull
-- name    : GlobalTheory.SheafPull.pull_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:49.8678+00:00
-- url     : https://prove2.me/theorems/947044cc-e65d-55b8-9170-dd60f6841745
-- title:
--   Sheaf Pull: pull pull
-- statement:
--   The Sheaf Pull construction uses the pull pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L321-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L321-L345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PushComparisonBijectiveOfIsClosedEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' u
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
open SheafLES Flasque
variable {X Y Z : TopCat.{u}}
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)] [HasExt.{w''} (AbSheaf Z)]

theorem GlobalTheory.SheafPull.pull_pull (f : Y ⟶ X) (g : Z ⟶ Y) {F : AbSheaf X} {G : AbSheaf Y} {L : AbSheaf Z}
    (φ : F ⟶ (push f).obj G) (ψ : G ⟶ (push g).obj L) (n : ℕ) {V : Opens X} {W : Opens Y}
    {T : Opens Z} (i : W ⟶ (Opens.map f).obj V) (k : T ⟶ (Opens.map g).obj W)
    (x : Sheaf.H'.{w} F n V) :
    pull.{w', w''} g ψ n k (pull.{w, w'} f φ n i x) =
      pull.{w, w''} (g ≫ f) (G := L) (φ ≫ (push f).map ψ) n (k ≫ (Opens.map g).map i) x := by sorry
