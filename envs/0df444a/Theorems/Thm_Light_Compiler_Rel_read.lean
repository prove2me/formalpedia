-- Prove2me | Theorems.Thm_Light_Compiler_Rel_read
-- name    : Light.Compiler.Rel.read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:18.683612+00:00
-- url     : https://prove2.me/theorems/0463206b-4632-4d5c-887b-fb5add50bfb9
-- title:
--   Rel: read
-- statement:
--   Reading a memory cell.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L280-L282
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L280-L282

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}

theorem Light.Compiler.Rel.read (R : Rel Z σ q m) {a : ℤ} (ha : Z.lim.Addr a) : m a = wd W (σ.mem a.toNat) := by sorry
