-- Prove2me | Theorems.Thm_Light_bounded_callFrame
-- name    : Light.bounded_callFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:47.931121+00:00
-- url     : https://prove2.me/theorems/ff389c28-b57c-44c7-aa37-1bbfe9ad7e22
-- title:
--   Light: bounded call Frame
-- statement:
--   The state in which a procedure starts is bounded, if the state of the caller is bounded and the
--   arguments of the call are safe.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L59-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L59-L63

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by sorry
