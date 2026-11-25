-- Prove2me | Theorems.Thm_GlobalTheory_T_splitThetaGridPath_avoids_opposite_corner
-- name    : GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:02.911687+00:00
-- url     : https://prove2.me/theorems/d195cd7b-0297-4be7-a4b6-c481a6a189be
-- title:
--   T: split Theta Grid Path avoids opposite corner
-- statement:
--   The T construction uses the split Theta Grid Path avoids opposite corner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCornerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SplitThetaGridPathAvoidsOppositeCornerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCornerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by sorry
