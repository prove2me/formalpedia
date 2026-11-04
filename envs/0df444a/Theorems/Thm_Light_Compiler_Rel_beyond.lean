-- Prove2me | Theorems.Thm_Light_Compiler_Rel_beyond
-- name    : Light.Compiler.Rel.beyond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:38.713359+00:00
-- url     : https://prove2.me/theorems/7875d26a-56c1-4178-b6a5-141721baf966
-- title:
--   Rel: beyond
-- statement:
--   A memory that differs only in scratch cells and in the stack beyond the frame represents the
--   same state.  (Here and below 1 ≤ q is needed because stack cell 0 is memory cell 0.)
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L251-L254
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L251-L254

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.beyond (R : Rel Z σ q m) (hq : 1 ≤ q)
    (A : AgreeOutside (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m m') : Rel Z σ q m' := by sorry
