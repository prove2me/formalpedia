-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_bodies
-- name    : Light.Compiler.codeAt_bodies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:44:03.773411+00:00
-- url     : https://prove2.me/theorems/efffb762-29fc-4718-804e-f4970d7f9fdf
-- title:
--   Compiler: code At bodies
-- statement:
--   Every body is at its entry, followed by the return sequence, and ends at or before the position
--   after the bodies.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L244-L257
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean#L244-L257

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)

theorem Light.Compiler.codeAt_bodies {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  := by sorry
