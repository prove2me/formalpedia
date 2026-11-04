-- Prove2me | Theorems.Thm_Light_Expr_abs_val_le
-- name    : Light.Expr.abs_val_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:17.984125+00:00
-- url     : https://prove2.me/theorems/d8772a54-bcde-453c-b538-f562c24742aa
-- title:
--   Expr: abs val le
-- statement:
--   The value of a safe expression in a bounded state fits in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L43-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/RunsStayInLimits.lean#L43-L50

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  := by sorry
