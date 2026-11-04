-- Prove2me | Theorems.Thm_Light_Compiler_scratch_subset_writable
-- name    : Light.Compiler.scratch_subset_writable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:26.259195+00:00
-- url     : https://prove2.me/theorems/0d7213a4-7714-424e-aaf3-955a30996ea6
-- title:
--   Compiler: scratch subset writable
-- statement:
--   A statement may change scratch cells.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L165-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L165-L166

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.scratch_subset_writable {q : ℕ} : Scratch Z.F ⊆ Writable Z q := by sorry
