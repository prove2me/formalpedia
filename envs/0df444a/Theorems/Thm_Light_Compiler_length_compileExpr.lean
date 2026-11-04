-- Prove2me | Theorems.Thm_Light_Compiler_length_compileExpr
-- name    : Light.Compiler.length_compileExpr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:43.997247+00:00
-- url     : https://prove2.me/theorems/3eecffe7-f518-4e47-8a03-88f67826da76
-- title:
--   Compiler: length compile Expr
-- statement:
--   The code of an expression has the length defined on the text.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L237-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L237-L242

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.length_compileExpr (e : Expr) (k : ℕ) : (compileExpr e k).length = e.size := by sorry
