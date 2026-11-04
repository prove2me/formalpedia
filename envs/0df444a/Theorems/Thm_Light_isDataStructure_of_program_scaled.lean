-- Prove2me | Theorems.Thm_Light_isDataStructure_of_program_scaled
-- name    : Light.isDataStructure_of_program_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:03.8083+00:00
-- url     : https://prove2.me/theorems/29a58f64-5a96-4016-bd4d-f1610c231830
-- title:
--   Light: is Data Structure of program scaled
-- statement:
--   If preprocessing, space and queries of the light program are at most A times bounds that are at
--   least 1 on the domain, those of the compiled programs are at most C times these bounds, where
--   C = timeConst · (A + 1).
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L379-L391
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L379-L391

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

theorem Light.isDataStructure_of_program_scaled {P : Program} {pPre pQ s k : ℕ} {extra : List ℤ}
    {dom : ThinPair → Prop} {Tp Sp Tq : ThinPair → ℝ} {A : ℝ}
    (h : ProgramIsDataStructure P pPre pQ s k extra dom (fun x => A * Tp x) (fun x => A * Sp x)
      fun x => A * Tq x)
    (h1 : ∀ x, dom x → 1 ≤ Tp x ∧ 1 ≤ Sp x ∧ 1 ≤ Tq x) :
    IsDataStructure (compileProgram P pPre false) (compileProgram P pQ false) cARG1 cARG2 cRESULT
      (slopeOf P false s k 2) extra dom (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Sp x)
      (fun x => ((timeConst P false : ℝ) * (A + 1)) * Tq x) := by sorry
