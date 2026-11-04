-- Prove2me | Theorems.Thm_Light_Compiler_Sizes_inRange_stack
-- name    : Light.Compiler.Sizes.inRange_stack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:12.46344+00:00
-- url     : https://prove2.me/theorems/2128bec0-19ef-44c8-88da-edc9da97de72
-- title:
--   Sizes: in Range stack
-- statement:
--   The addresses of the stack fit in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L198-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L198-L200

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.Sizes.inRange_stack (Z : Sizes W) {j : ℕ} (hj : j ≤ Z.Q) : InRange W (cStack j) := by sorry
