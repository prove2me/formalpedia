-- Prove2me | Theorems.Thm_Light_Compiler_agreeOutside_startMem
-- name    : Light.Compiler.agreeOutside_startMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:53.946142+00:00
-- url     : https://prove2.me/theorems/802f595a-1672-41af-8064-20b5a5a09c71
-- title:
--   Compiler: agree Outside start Mem
-- statement:
--   The start-up code changes only the registers for 1, 0, -1, the pool, FP and the outermost
--   frame.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L189-L191
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/StartUp.lean#L189-L191

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.agreeOutside_startMem (h3 : 3 ≤ F) (N : ℕ) (m : ℤ → BitVec W) :
    AgreeOutside (Constants N ∪ ({cFP} ∪ MainFrame F)) m (startMem F N m) := by sorry
