-- Prove2me | Theorems.Thm_Light_Stmt_width_set_le_iff
-- name    : Light.Stmt.width_set_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:52.024483+00:00
-- url     : https://prove2.me/theorems/60df76ac-9f35-4e52-b97b-ded8b9ee80e3
-- title:
--   Stmt: width set le iff
-- statement:
--   The Stmt construction uses the width set le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L344-L344
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L344-L344

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Stmt.width_set_le_iff : (Stmt.set x e).width ≤ F ↔ x < F ∧ e.width ≤ F := by sorry
