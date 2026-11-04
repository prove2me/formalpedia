-- Prove2me | Theorems.Thm_Light_Expr_width_le_iff
-- name    : Light.Expr.width_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:53.061051+00:00
-- url     : https://prove2.me/theorems/23273628-d7ed-46f6-a1c9-651fcdf8ca5e
-- title:
--   Expr: width le iff
-- statement:
--   The Expr construction uses the width le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L338-L338
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L338-L338

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Expr.width_le_iff : e.width ≤ F ↔ e.vars ≤ F ∧ e.height ≤ F := by sorry
