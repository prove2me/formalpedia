-- Prove2me | Theorems.Thm_Light_Compiler_steps_pair
-- name    : Light.Compiler.steps_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:57.681204+00:00
-- url     : https://prove2.me/theorems/e058ac4e-b092-4c0c-9a6c-8407993bea74
-- title:
--   Compiler: steps pair
-- statement:
--   The code of two expressions, one after the other, leaves their values in T₀ and T₁ and changes
--   scratch cells only.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L45-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L45-L57

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

theorem Light.Compiler.steps_pair (I : Framed Z σ q m)
    (hcode : CodeAt code pos (compileExpr a 0 ++ compileExpr b 1 ++ rest)) (hwa : a.width ≤ Z.F)
    (hwb : b.width ≤ Z.F) (hsa : a.Safe Z.lim σ) (hsb : b.Safe Z.lim σ) :
    ∃ m', Steps code (a.size + b.size) ⟨pos, m⟩ ⟨pos + (a.size + b.size), m'⟩ ∧
      m' (cT 0) = wd W (a.val σ) ∧ m' (cT 1) = wd W (b.val σ) ∧
      AgreeOutside (Scratch Z.F) m m' := by sorry
