-- Prove2me | Theorems.Thm_Light_Compiler_writable_subset_writable
-- name    : Light.Compiler.writable_subset_writable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:37.996194+00:00
-- url     : https://prove2.me/theorems/8ed09b73-0c0b-4e90-9cf4-58f36c89f627
-- title:
--   Compiler: writable subset writable
-- statement:
--   A statement in a later frame may change less.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L173-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L173-L174

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.writable_subset_writable {q q' : ℕ} (h : q ≤ q') : Writable Z q' ⊆ Writable Z q := by sorry
