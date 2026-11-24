-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsPath_pairwise_lt_source_index_difference_along_path
-- name    : GlobalTheory.SplitFlip.IsPath.pairwise_lt_source_index_difference_along_path
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:58.882393+00:00
-- url     : https://prove2.me/theorems/4a8cea69-d3f9-44bd-9335-4ccc023ba843
-- title:
--   Is Path: pairwise lt source index difference along path
-- statement:
--   The Is Path construction uses the pairwise lt source index difference along path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquare.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquare.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip

theorem GlobalTheory.SplitFlip.IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by sorry
