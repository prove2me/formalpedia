-- Prove2me | Theorems.Thm_Light_Compiler_length_dispatcher
-- name    : Light.Compiler.length_dispatcher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:07:00.89708+00:00
-- url     : https://prove2.me/theorems/676d5009-5be5-4b8b-9c16-ef0b20896b9a
-- title:
--   Compiler: length dispatcher
-- statement:
--   Two instructions for each position.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Dispatcher.lean#L37-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Dispatcher.lean#L37-L38

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}

theorem Light.Compiler.length_dispatcher (n : ℕ) : (dispatcher n).length = 2 * n := by sorry
