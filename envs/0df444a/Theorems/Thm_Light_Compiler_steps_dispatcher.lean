-- Prove2me | Theorems.Thm_Light_Compiler_steps_dispatcher
-- name    : Light.Compiler.steps_dispatcher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:36.322743+00:00
-- url     : https://prove2.me/theorems/ff311101-31c2-4850-96d3-cd6a65345289
-- title:
--   Compiler: steps dispatcher
-- statement:
--   From the beginning of the dispatcher, with the position r in RR, the machine arrives at position
--   r after 2 (r + 1) steps; RR then holds -1, and no other cell has changed.  The positions fit in a
--   word (hn).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Dispatcher.lean#L89-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Dispatcher.lean#L89-L94

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}

theorem Light.Compiler.steps_dispatcher {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n)
    (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W) (m : ℤ → BitVec W) (hone : m cONE = wd W 1)
    (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ := by sorry
