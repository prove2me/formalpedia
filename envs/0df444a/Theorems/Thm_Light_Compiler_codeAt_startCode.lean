-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_startCode
-- name    : Light.Compiler.codeAt_startCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:57.482649+00:00
-- url     : https://prove2.me/theorems/2306db1a-00ec-4c89-90ce-b1399c9b2499
-- title:
--   Compiler: code At start Code
-- statement:
--   The start-up code follows the dispatcher.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L236-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L236-L238

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_startCode :
    CodeAt (compileProgram P p0 dec) (3 * dispPos P dec) (startCode P dec) := by sorry
