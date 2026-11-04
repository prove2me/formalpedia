-- Prove2me | Theorems.Thm_Light_fits_of_small
-- name    : Light.fits_of_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:33.924012+00:00
-- url     : https://prove2.me/theorems/b6e7917c-ed5c-41ec-a23f-0e79438f832f
-- title:
--   Light: fits of small
-- statement:
--   Limits that are polynomial in the parameters fit every admissible word size.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L115-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/ToMachine.lean#L115-L147

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

theorem Light.fits_of_small {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by sorry
