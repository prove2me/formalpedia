-- Prove2me | Theorems.Thm_GlobalTheory_FlipPathPairwise_srcDiff_of_join
-- name    : GlobalTheory.FlipPathPairwise.srcDiff_of_join
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:53.432919+00:00
-- url     : https://prove2.me/theorems/38dd533c-c291-4a30-a6c4-cbbdb6ce0ce4
-- title:
--   Flip Path Pairwise: src Diff of join
-- statement:
--   The Flip Path Pairwise construction uses the src Diff of join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSplitThetaGridPathFlipGridPathAtSquare.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSplitThetaGridPathFlipGridPathAtSquare.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSplitThetaGridPathFlipGridPathAtSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
open GlobalTheory GlobalTheory.FlipPathPairwise

theorem GlobalTheory.FlipPathPairwise.srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by sorry
