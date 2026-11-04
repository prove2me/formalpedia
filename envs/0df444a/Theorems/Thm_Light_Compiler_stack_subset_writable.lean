-- Prove2me | Theorems.Thm_Light_Compiler_stack_subset_writable
-- name    : Light.Compiler.stack_subset_writable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:11.918432+00:00
-- url     : https://prove2.me/theorems/12ab7556-38c0-4489-a142-cbaa53107025
-- title:
--   Compiler: stack subset writable
-- statement:
--   A statement may change the stack from its frame on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L169-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L169-L170

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.stack_subset_writable {q : ℕ} : Stack q Z.Q ⊆ Writable Z q := by sorry
