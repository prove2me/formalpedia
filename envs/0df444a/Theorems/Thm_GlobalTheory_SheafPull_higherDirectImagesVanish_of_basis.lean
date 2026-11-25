-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_higherDirectImagesVanish_of_basis
-- name    : GlobalTheory.SheafPull.higherDirectImagesVanish_of_basis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:12.885921+00:00
-- url     : https://prove2.me/theorems/81b0bc57-8d5a-5e77-8c67-e12764c09ff8
-- title:
--   Sheaf Pull: higher Direct Images Vanish of basis
-- statement:
--   The Sheaf Pull construction uses the higher Direct Images Vanish of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L228-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L228-L233

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
omit [HasExt.{w} (AbSheaf X)]

theorem GlobalTheory.SheafPull.higherDirectImagesVanish_of_basis (G : AbSheaf Y)
    (h : ∀ (V : Opens X), ∀ x ∈ V, ∃ W ≤ V, x ∈ W ∧
      ∀ n, 0 < n → Subsingleton (Sheaf.H'.{w'} G n ((Opens.map f).obj W))) :
    HigherDirectImagesVanish.{w'} f G := by sorry
