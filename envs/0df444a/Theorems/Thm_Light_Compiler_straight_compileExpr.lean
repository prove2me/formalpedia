-- Prove2me | Theorems.Thm_Light_Compiler_straight_compileExpr
-- name    : Light.Compiler.straight_compileExpr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:11:51.346079+00:00
-- url     : https://prove2.me/theorems/8b024213-f9fb-476c-954d-5ac621016ee4
-- title:
--   Compiler: straight compile Expr
-- statement:
--   The code of an expression only changes the memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Expressions.lean#L94-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Expressions.lean#L94-L99

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F : ℕ}

theorem Light.Compiler.straight_compileExpr : ∀ (e : Expr) (k : ℕ), ∀ i ∈ compileExpr e k, Straight i
  := by sorry
