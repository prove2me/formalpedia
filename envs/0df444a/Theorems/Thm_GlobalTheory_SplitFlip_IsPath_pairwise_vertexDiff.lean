-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsPath_pairwise_vertexDiff
-- name    : GlobalTheory.SplitFlip.IsPath.pairwise_vertexDiff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:09.12082+00:00
-- url     : https://prove2.me/theorems/1651c8c2-0acb-4c5f-b70e-1b24690bb328
-- title:
--   Is Path: pairwise vertex Diff
-- statement:
--   The Is Path construction uses the pairwise vertex Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCorner.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCorner.lean#L11-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip

theorem GlobalTheory.SplitFlip.IsPath.pairwise_vertexDiff : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src
  := by sorry
