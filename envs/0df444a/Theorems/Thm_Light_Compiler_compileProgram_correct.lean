-- Prove2me | Theorems.Thm_Light_Compiler_compileProgram_correct
-- name    : Light.Compiler.compileProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:23:25.442716+00:00
-- url     : https://prove2.me/theorems/24f9f33f-0234-4535-9123-a6d6717c4065
-- title:
--   Compiler: compile Program correct
-- statement:
--   **The compiler is correct.**  Let the call of procedure p0 of the program P on the arguments i,
--   j and the memory μ end after c steps within the limits, and let the word size fit the limits.  Then
--   the compiled program, started on any memory whose cells `a ≥ 0` hold the words of μ and whose
--   cells -1 and -2 hold i and j, gives its verdict within `startCost + stepsPerStep · c` steps.  Then
--   the cell -3 holds the result of the procedure and the cells `a ≥ 0` hold the final memory.  The
--   cells -1 and -2, the cells below `-lowCell` and the cells from `lim.space` on are unchanged.  The
--   two constants of the time depend on the text of P and on dec only.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/WholeProgram.lean#L224-L263
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/WholeProgram.lean#L224-L263

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr exec)
variable {W : ℕ}

theorem Light.Compiler.compileProgram_correct {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ}
    {i j : ℤ} {σ' : State} {c : ℕ} {m : ℤ → BitVec W}
    (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W, exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m
        = some (verdictOf dec (σ'.loc 0), m') ∧ Outcome lim P dec m σ' m' := by sorry
