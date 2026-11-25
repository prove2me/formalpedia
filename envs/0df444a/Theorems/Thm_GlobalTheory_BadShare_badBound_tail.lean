-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_badBound_tail
-- name    : GlobalTheory.BadShare.badBound_tail
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:28.786814+00:00
-- url     : https://prove2.me/theorems/291ee65d-2938-513d-bef6-1ada69b9a989
-- title:
--   Bad Share: bad Bound tail
-- statement:
--   The Bad Share construction uses the bad Bound tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LogDivSqrtLeFourExp.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LogDivSqrtLeFourExp.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LogDivSqrtLeFourExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.badBound_tail (eps C : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in Filter.atTop,
      612 * (x ^ C) ^ 3 * Real.exp (-(x ^ (eps / 6))) ≤ Real.exp (-(x ^ (eps / 7))) := by sorry
