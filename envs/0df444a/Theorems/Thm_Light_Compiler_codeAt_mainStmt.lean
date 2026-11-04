-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_mainStmt
-- name    : Light.Compiler.codeAt_mainStmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:38.46564+00:00
-- url     : https://prove2.me/theorems/ac7fc036-d55d-4c8b-9d7a-22bdde8db376
-- title:
--   Compiler: code At main Stmt
-- statement:
--   The outermost statement is at `mainPos`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L212-L215
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L212-L215

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_mainStmt :
    CodeAt (compileProgram P p0 dec) mainPos
      (compileStmt (codeLayout P dec) (mainStmt p0) mainPos) := by sorry
