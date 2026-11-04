-- Prove2me | Theorems.Thm_Light_Compiler_width_mainStmt
-- name    : Light.Compiler.width_mainStmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:35.067498+00:00
-- url     : https://prove2.me/theorems/f08797cd-635a-4265-b3e8-17ccb47371ce
-- title:
--   Compiler: width main Stmt
-- statement:
--   The outermost statement uses the local variables 0, 1, 2.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L155-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L155-L155

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.width_mainStmt (p0 : ℕ) : (mainStmt p0).width = 3 := by sorry
