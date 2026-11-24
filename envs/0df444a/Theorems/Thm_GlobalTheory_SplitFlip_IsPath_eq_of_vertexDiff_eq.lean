-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsPath_eq_of_vertexDiff_eq
-- name    : GlobalTheory.SplitFlip.IsPath.eq_of_vertexDiff_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:17.173812+00:00
-- url     : https://prove2.me/theorems/76bb0cfb-db8b-4bcd-a24f-55c254cdae5c
-- title:
--   Is Path: eq of vertex Diff eq
-- statement:
--   The Is Path construction uses the eq of vertex Diff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCorner.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCorner.lean#L26-L42

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

theorem GlobalTheory.SplitFlip.IsPath.eq_of_vertexDiff_eq {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : vertexDiff a.src = vertexDiff b.src) : a = b := by sorry
