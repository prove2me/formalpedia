-- Prove2me | Theorems.Thm_Light_Compiler_two_mul_frameSize_add_le_dispPos
-- name    : Light.Compiler.two_mul_frameSize_add_le_dispPos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:08.415305+00:00
-- url     : https://prove2.me/theorems/32808dc3-aaca-4933-ad87-0e9e4d6c6920
-- title:
--   Compiler: two mul frame Size add le disp Pos
-- statement:
--   The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
--   statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
--   two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
--   pointer, and it reaches further down than the 2 F + 1 temporaries.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L165-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L165-L170

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.two_mul_frameSize_add_le_dispPos (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by sorry
