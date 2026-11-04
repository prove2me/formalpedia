-- Prove2me | Theorems.Thm_Light_Compiler_cStack_add
-- name    : Light.Compiler.cStack_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:14.775376+00:00
-- url     : https://prove2.me/theorems/0c4c959c-8076-4e52-9617-71be41634d6d
-- title:
--   Compiler: c Stack add
-- statement:
--   Back from the frame q + x to the frame q.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L189-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L189-L192

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.cStack_add (q x : ℕ) : cStack (q + x) + ((2 * x : ℕ) : ℤ) = cStack q := by sorry
