-- Prove2me | Theorems.Thm_Light_Compiler_size_mainStmt
-- name    : Light.Compiler.size_mainStmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:15:11.659907+00:00
-- url     : https://prove2.me/theorems/49062c9c-9d89-44d8-877b-698f28a33f03
-- title:
--   Compiler: size main Stmt
-- statement:
--   The length of the outermost statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L151-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L151-L152

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.size_mainStmt (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by sorry
