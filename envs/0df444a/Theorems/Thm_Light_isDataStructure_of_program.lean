-- Prove2me | Theorems.Thm_Light_isDataStructure_of_program
-- name    : Light.isDataStructure_of_program
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:43.805963+00:00
-- url     : https://prove2.me/theorems/8b53fd64-60cf-4a43-8e72-73272c9476e2
-- title:
--   Light: is Data Structure of program
-- statement:
--   **The two compiled programs are a data structure on the word RAM**: queries are put into the
--   cells -1 and -2 (`cARG1`, `cARG2`) and answered in the cell -3 (`cRESULT`).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L338-L355
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L338-L355

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

theorem Light.isDataStructure_of_program {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom Tp Sp Tq) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom
      (fun x => (timeConst P false : ℝ) * Tp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Sp x + timeConst P false)
      (fun x => (timeConst P false : ℝ) * Tq x + timeConst P false) := by sorry
