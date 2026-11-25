-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_pull_eq
-- name    : GlobalTheory.SheafPull.pull_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:45.461833+00:00
-- url     : https://prove2.me/theorems/e9f46dad-4fa1-5dab-a2af-5d58c0441c4b
-- title:
--   Sheaf Pull: pull eq
-- statement:
--   The Sheaf Pull construction uses the pull eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L189-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L189-L192

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
variable {X Y : TopCat.{u}}
variable [HasExt.{w} (AbSheaf X)] [HasExt.{w'} (AbSheaf Y)]
variable (f : Y ⟶ X)

theorem GlobalTheory.SheafPull.pull_eq {F : AbSheaf X} {G : AbSheaf Y} (φ : F ⟶ (push f).obj G) (n : ℕ)
    {V : Opens X} {W : Opens Y} (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{w} F n V) :
    pull.{w, w'} f φ n i x = res G n i (pushComparison.{w, w'} f G n V (map φ n V x)) := by sorry
