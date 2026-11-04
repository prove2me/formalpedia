-- Prove2me | Theorems.Thm_Light_Compiler_length_compileStmt
-- name    : Light.Compiler.length_compileStmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:47.210953+00:00
-- url     : https://prove2.me/theorems/1d81c031-248c-45ca-a774-bbf6b55f97b6
-- title:
--   Compiler: length compile Stmt
-- statement:
--   The code of a statement has the length defined on the text.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L270-L279
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L270-L279

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.length_compileStmt (G : CodeLayout) (s : Stmt) (pos : ℕ) :
    (compileStmt G s pos).length = s.size G.F := by sorry
