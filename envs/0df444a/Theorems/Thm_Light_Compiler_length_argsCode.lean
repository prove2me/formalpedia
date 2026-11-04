-- Prove2me | Theorems.Thm_Light_Compiler_length_argsCode
-- name    : Light.Compiler.length_argsCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:10.860932+00:00
-- url     : https://prove2.me/theorems/9cc84f34-b6b6-4445-b874-ce4aa0a0218f
-- title:
--   Compiler: length args Code
-- statement:
--   The code for the arguments of a call has the length defined on the text.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L249-L252
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L249-L252

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.length_argsCode (es : List Expr) (k : ℕ) : (argsCode es k).length = argsSize es := by sorry
