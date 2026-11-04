-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_dispatcher_dispPos
-- name    : Light.Compiler.codeAt_dispatcher_dispPos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:55.412398+00:00
-- url     : https://prove2.me/theorems/8e198b8e-dcbd-4fc7-90e8-6b571182478f
-- title:
--   Compiler: code At dispatcher disp Pos
-- statement:
--   The dispatcher is at `dispPos`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L231-L233
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L231-L233

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_dispatcher_dispPos :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) := by sorry
