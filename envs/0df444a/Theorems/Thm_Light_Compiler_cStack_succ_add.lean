-- Prove2me | Theorems.Thm_Light_Compiler_cStack_succ_add
-- name    : Light.Compiler.cStack_succ_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:32.884748+00:00
-- url     : https://prove2.me/theorems/363e8de5-a780-428c-b5e7-7b2a6e3513ce
-- title:
--   Compiler: c Stack succ add
-- statement:
--   The stack cell before the cell q + 1.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L195-L195
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L195-L195

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.cStack_succ_add (q : ℕ) : cStack (q + 1) + ((2 : ℕ) : ℤ) = cStack q := by sorry
