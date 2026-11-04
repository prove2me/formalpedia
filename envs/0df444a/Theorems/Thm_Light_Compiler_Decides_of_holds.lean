-- Prove2me | Theorems.Thm_Light_Compiler_Decides_of_holds
-- name    : Light.Compiler.Decides.of_holds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:48.806275+00:00
-- url     : https://prove2.me/theorems/733824a6-54c9-40c6-9b5b-b190e6d4588d
-- title:
--   Decides: of holds
-- statement:
--   The test holds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L69-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean#L69-L73

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

theorem Light.Compiler.Decides.of_holds {F size : ℕ} {p : Prop} (h : Decides code F pos size l m p) (hp : p) :
    ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
      Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩ := by sorry
