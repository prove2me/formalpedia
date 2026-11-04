-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_tailCode
-- name    : Light.Compiler.codeAt_tailCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:37.440019+00:00
-- url     : https://prove2.me/theorems/a2852e4e-7403-4067-b9ce-a1237a423176
-- title:
--   Compiler: code At tail Code
-- statement:
--   The code for the verdict follows the outermost statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L218-L222
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L218-L222

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_tailCode :
    CodeAt (compileProgram P p0 dec) (tailPos (frameSize P))
      (tailCode dec (tailPos (frameSize P))) := by sorry
