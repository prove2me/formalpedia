-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_headCode
-- name    : Light.Compiler.codeAt_headCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:33.166416+00:00
-- url     : https://prove2.me/theorems/113e2bde-c3b6-45c9-bdab-ed4e8ac208ba
-- title:
--   Compiler: code At head Code
-- statement:
--   The first part is at position 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L205-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L205-L206

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable (P : Program) (p0 : ℕ) (dec : Bool)

theorem Light.Compiler.codeAt_headCode : CodeAt (compileProgram P p0 dec) 0 (headCode P dec) := by sorry
