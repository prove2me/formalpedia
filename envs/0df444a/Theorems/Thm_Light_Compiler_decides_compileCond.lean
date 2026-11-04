-- Prove2me | Theorems.Thm_Light_Compiler_decides_compileCond
-- name    : Light.Compiler.decides_compileCond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:29.596534+00:00
-- url     : https://prove2.me/theorems/00610a76-0fdd-4aec-b0f9-120bb746918c
-- title:
--   Compiler: decides compile Cond
-- statement:
--   The code of a test decides the test.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L141-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L141-L146

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

theorem Light.Compiler.decides_compileCond (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by sorry
