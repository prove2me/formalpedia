-- Prove2me | Theorems.Thm_Light_Compiler_steps_setVar
-- name    : Light.Compiler.steps_setVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:59.354202+00:00
-- url     : https://prove2.me/theorems/e1a60fb2-9761-4465-9e84-53c82b0aeca3
-- title:
--   Compiler: steps set Var
-- statement:
--   The two instructions that put the content v of the cell c into the local variable x.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L313-L331
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean#L313-L331

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update

set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {F : ℕ}
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}

theorem Light.Compiler.steps_setVar {x : ℕ} {c v : ℤ} (I : Framed Z σ q m) (hx : x < Z.F)
    (hcode : CodeAt code pos (.sub cADDR cFP (cPool (2 * x)) :: .store cADDR c :: rest))
    (hc : m c = wd W v) (hne : c ≠ cADDR) :
    ∃ m', Steps code 2 ⟨pos, m⟩ ⟨pos + 2, m'⟩ ∧
      Rel Z { σ with loc := Function.update σ.loc x v } q m' ∧
      AgreeOutside (Writable Z q) m m' := by sorry
