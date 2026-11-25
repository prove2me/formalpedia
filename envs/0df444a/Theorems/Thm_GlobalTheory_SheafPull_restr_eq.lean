-- Prove2me | Theorems.Thm_GlobalTheory_SheafPull_restr_eq
-- name    : GlobalTheory.SheafPull.restr_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:56.914483+00:00
-- url     : https://prove2.me/theorems/136d7f36-b806-50bb-a57e-8a612714676a
-- title:
--   Sheaf Pull: restr eq
-- statement:
--   The Sheaf Pull construction uses the restr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PushComparisonBijectiveOfIsClosedEmbedding.lean#L29-L30

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

theorem GlobalTheory.SheafPull.restr_eq {j : Y ⟶ X} (hj : Topology.IsOpenEmbedding j) :
    restr hj = hj.sheafPullback AddCommGrpCat.{u} := by sorry
