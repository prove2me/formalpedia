-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_bodiesCode
-- name    : Light.Compiler.codeAt_bodiesCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:40.101967+00:00
-- url     : https://prove2.me/theorems/d651a3d5-3282-490f-9f48-78b8282a5693
-- title:
--   Compiler: code At bodies Code
-- statement:
--   The bodies begin at `firstBody`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L225-L228
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L225-L228

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_bodiesCode :
    CodeAt (compileProgram P p0 dec) (firstBody (frameSize P) dec)
      (bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)) := by sorry
