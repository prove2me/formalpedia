-- Prove2me | Theorems.Thm_Light_Stmt_width_ite_le_iff
-- name    : Light.Stmt.width_ite_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:55.443992+00:00
-- url     : https://prove2.me/theorems/ebe317fa-2ff8-4159-a4c2-396eb7919da9
-- title:
--   Stmt: width ite le iff
-- statement:
--   The Stmt construction uses the width ite le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L351-L353
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L351-L353

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Stmt.width_ite_le_iff :
    (Stmt.ite c s t).width ≤ F ↔ c.width ≤ F ∧ s.width ≤ F ∧ t.width ≤ F := by sorry
