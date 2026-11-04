-- Prove2me | Theorems.Thm_Light_Cond_width_eq_le_iff
-- name    : Light.Cond.width_eq_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:41:51.28727+00:00
-- url     : https://prove2.me/theorems/65995166-d8a9-4d4f-8d4b-ff8ac5f7dba5
-- title:
--   Cond: width eq le iff
-- statement:
--   The Cond construction uses the width eq le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L342-L342
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L342-L342

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.Cond.width_eq_le_iff : (Cond.eq a b).width ≤ F ↔ a.width ≤ F ∧ b.width ≤ F := by sorry
