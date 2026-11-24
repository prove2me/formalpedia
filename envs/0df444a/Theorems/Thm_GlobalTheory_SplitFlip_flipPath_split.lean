-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_flipPath_split
-- name    : GlobalTheory.SplitFlip.flipPath_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:20:23.484206+00:00
-- url     : https://prove2.me/theorems/73421762-a77d-4eb8-85f6-7ed0a103c0c0
-- title:
--   Split Flip: flip Path split
-- statement:
--   The Split Flip construction uses the flip Path split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlipGridPathAtSquareSplit.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlipGridPathAtSquareSplit.lean#L34-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitFlip.PathSplit

theorem GlobalTheory.SplitFlip.flipPath_split : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := by sorry
