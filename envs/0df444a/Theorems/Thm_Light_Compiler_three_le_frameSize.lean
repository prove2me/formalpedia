-- Prove2me | Theorems.Thm_Light_Compiler_three_le_frameSize
-- name    : Light.Compiler.three_le_frameSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:57.920931+00:00
-- url     : https://prove2.me/theorems/6c6ada79-fbca-4190-bc64-beaaef5c23d7
-- title:
--   Compiler: three le frame Size
-- statement:
--   The outermost frame has room for the result and the two arguments.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L50-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L50-L50

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.three_le_frameSize (P : Program) : 3 ≤ frameSize P := by sorry
