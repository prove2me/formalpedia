-- Prove2me | Theorems.Thm_Light_Stmt_width_call_le_iff
-- name    : Light.Stmt.width_call_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:58.545358+00:00
-- url     : https://prove2.me/theorems/4c7c3082-5d2e-40af-90de-3f9aa1d5ec51
-- title:
--   Stmt: width call le iff
-- statement:
--   The Stmt construction uses the width call le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L358-L360
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L358-L360

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Stmt.width_call_le_iff :
    (Stmt.call p args x).width ≤ F ↔ x < F ∧ args.length ≤ F ∧ ∀ e ∈ args, e.width ≤ F := by sorry
