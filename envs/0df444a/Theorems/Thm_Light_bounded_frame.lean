-- Prove2me | Theorems.Thm_Light_bounded_frame
-- name    : Light.bounded_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:47.94532+00:00
-- url     : https://prove2.me/theorems/fe875927-01f6-42ae-b625-769ee7593877
-- title:
--   Light: bounded frame
-- statement:
--   A frame that holds words, over a memory that holds words, is a bounded state.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L53-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L53-L55

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ := by sorry
