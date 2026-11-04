-- Prove2me | Theorems.Thm_Light_Compiler_codeAt_after_pair
-- name    : Light.Compiler.codeAt_after_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:54.381216+00:00
-- url     : https://prove2.me/theorems/bf327fc8-cb7b-4549-aee2-436ab7e8e6fa
-- title:
--   Compiler: code At after pair
-- statement:
--   What follows the code of two expressions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L39-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L39-L41

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

theorem Light.Compiler.codeAt_after_pair (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) :
    CodeAt code (pos + (a.size + b.size)) rest := by sorry
