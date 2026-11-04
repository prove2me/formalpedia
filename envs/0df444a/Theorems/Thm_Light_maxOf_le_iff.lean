-- Prove2me | Theorems.Thm_Light_maxOf_le_iff
-- name    : Light.maxOf_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:22.367411+00:00
-- url     : https://prove2.me/theorems/1e1099f6-c981-4810-badb-d1edad2b8eff
-- title:
--   Light: max Of le iff
-- statement:
--   The Light construction uses the max Of le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L333-L334
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L333-L334

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light
variable {F x p : ℕ} {o : Op} {a b e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}

theorem Light.maxOf_le_iff {α : Type} {f : α → ℕ} {l : List α} : maxOf f l ≤ F ↔ ∀ y ∈ l, f y ≤ F := by sorry
