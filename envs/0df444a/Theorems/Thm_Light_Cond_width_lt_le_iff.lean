-- Prove2me | Theorems.Thm_Light_Cond_width_lt_le_iff
-- name    : Light.Cond.width_lt_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:49.991903+00:00
-- url     : https://prove2.me/theorems/cc9bc4f5-4d55-4cc7-9e76-976e5d7edbf2
-- title:
--   Cond: width lt le iff
-- statement:
--   The Cond construction uses the width lt le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L340-L340
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L340-L340

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Cond.width_lt_le_iff : (Cond.lt a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := by sorry
