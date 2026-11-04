-- Prove2me | Theorems.Thm_Light_Compiler_Sizes_inRange_neg_one
-- name    : Light.Compiler.Sizes.inRange_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:34.28812+00:00
-- url     : https://prove2.me/theorems/deec4d38-7f42-4787-bf7e-342638927418
-- title:
--   Sizes: in Range neg one
-- statement:
--   The number -1, on which every jump branches, fits in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L207-L210
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L207-L210

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.Sizes.inRange_neg_one (Z : Sizes W) : InRange W (-1) := by sorry
