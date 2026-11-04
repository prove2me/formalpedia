-- Prove2me | Theorems.Thm_Light_Compiler_cStack_sub
-- name    : Light.Compiler.cStack_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:22.357467+00:00
-- url     : https://prove2.me/theorems/8179f0eb-aedf-4127-b26a-cb98f3e03c62
-- title:
--   Compiler: c Stack sub
-- statement:
--   The cell of the local variable x of the frame q, computed from FP and the pool.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L183-L186
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L183-L186

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.cStack_sub (q x : ℕ) : cStack q - ((2 * x : ℕ) : ℤ) = cStack (q + x) := by sorry
