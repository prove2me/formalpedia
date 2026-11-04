-- Prove2me | Theorems.Thm_Light_Expr_vars_op_le_iff
-- name    : Light.Expr.vars_op_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:47.423204+00:00
-- url     : https://prove2.me/theorems/1f2b13a6-e907-40cd-8f71-966189b214b9
-- title:
--   Expr: vars op le iff
-- statement:
--   The Expr construction uses the vars op le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L336-L336
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L336-L336

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Expr.vars_op_le_iff : (Expr.op o a b).vars ≤ F ↔ a.vars ≤ F ∧ b.vars ≤ F := by sorry
