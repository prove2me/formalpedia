-- Prove2me | Theorems.Thm_Light_Compiler_length_compileCond
-- name    : Light.Compiler.length_compileCond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:12.425162+00:00
-- url     : https://prove2.me/theorems/43f7f6be-c824-4816-a63b-4c2029000c47
-- title:
--   Compiler: length compile Cond
-- statement:
--   The code of a test has the length defined on the text.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L245-L246
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean#L245-L246

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Mathlib.Data.Nat.Digits.Defs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
set_option autoImplicit false
section
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.length_compileCond (c : Cond) (l : ℕ) : (compileCond c l).length = c.size := by sorry
