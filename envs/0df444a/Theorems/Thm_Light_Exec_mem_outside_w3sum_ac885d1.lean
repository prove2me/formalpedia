-- Prove2me | Theorems.Thm_Light_Exec_mem_outside_w3sum_ac885d1
-- name    : Light.Exec.mem_outside_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:48.335812+00:00
-- url     : https://prove2.me/theorems/c1bf5940-3167-4a7f-b93d-0537202deb35
-- title:
--   Exec: mem outside
-- statement:
--   A run does not change the cells from lim.space on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L82-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L82-L95

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Exec.mem_outside_w3sum_ac885d1 {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by sorry
