-- Prove2me | Theorems.Thm_Light_Compiler_Sizes_inRange_addr
-- name    : Light.Compiler.Sizes.inRange_addr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:32.690296+00:00
-- url     : https://prove2.me/theorems/21ef7528-ce89-4803-a5e8-dc3af175d950
-- title:
--   Sizes: in Range addr
-- statement:
--   The addresses of the memory fit in a word.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L203-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L203-L204

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.Sizes.inRange_addr (Z : Sizes W) {a : ℤ} (h : Z.lim.Addr a) : InRange W a := by sorry
