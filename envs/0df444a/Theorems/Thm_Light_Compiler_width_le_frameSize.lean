-- Prove2me | Theorems.Thm_Light_Compiler_width_le_frameSize
-- name    : Light.Compiler.width_le_frameSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:29.910538+00:00
-- url     : https://prove2.me/theorems/bb66c298-1029-4480-8355-c85dea6db9c6
-- title:
--   Compiler: width le frame Size
-- statement:
--   Every body fits into a frame.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L53-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L53-L54

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.width_le_frameSize {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P := by sorry
