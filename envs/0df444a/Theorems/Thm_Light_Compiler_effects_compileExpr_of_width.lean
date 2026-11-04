-- Prove2me | Theorems.Thm_Light_Compiler_effects_compileExpr_of_width
-- name    : Light.Compiler.effects_compileExpr_of_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:11:50.02817+00:00
-- url     : https://prove2.me/theorems/05300930-3dfa-48bd-922c-9e1e8cfc1745
-- title:
--   Compiler: effects compile Expr of width
-- statement:
--   The code of an expression of width at most F, when there are F temporaries from T_k on, leaves
--   its value in T_k and changes nothing but ADDR and the temporaries from T_k on.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Expressions.lean#L159-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Expressions.lean#L159-L164

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F : ℕ}
variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.effects_compileExpr_of_width (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F)
    (hs : e.Safe Z.lim σ) (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧
      AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) := by sorry
