-- Prove2me | Theorems.Thm_Light_Compiler_straight_argsCode
-- name    : Light.Compiler.straight_argsCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:26.887197+00:00
-- url     : https://prove2.me/theorems/01f2f96d-782e-489b-8b90-2cd7edc342fc
-- title:
--   Compiler: straight args Code
-- statement:
--   The code of the arguments only changes the memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L32-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L32-L34

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.straight_argsCode : ∀ (es : List Expr) (k : ℕ), ∀ i ∈ argsCode es k, Straight i
  := by sorry
