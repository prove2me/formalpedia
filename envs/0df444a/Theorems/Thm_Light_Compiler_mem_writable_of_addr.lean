-- Prove2me | Theorems.Thm_Light_Compiler_mem_writable_of_addr
-- name    : Light.Compiler.mem_writable_of_addr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:37.226932+00:00
-- url     : https://prove2.me/theorems/15fdb4dd-f8b3-4abb-aebc-aed58b9a33fc
-- title:
--   Compiler: mem writable of addr
-- statement:
--   A statement may change the memory cells within the limits.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L177-L178
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L177-L178

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}

theorem Light.Compiler.mem_writable_of_addr {q : ℕ} {a : ℤ} (h : Z.lim.Addr a) : a ∈ Writable Z q := by sorry
