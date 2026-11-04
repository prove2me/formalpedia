-- Prove2me | Theorems.Thm_Light_Compiler_straight_newFrame
-- name    : Light.Compiler.straight_newFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:31.04284+00:00
-- url     : https://prove2.me/theorems/75ba6971-607d-42eb-ac03-3830535852c1
-- title:
--   Compiler: straight new Frame
-- statement:
--   The code of the new frame only changes the memory.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L96-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/CallFrames.lean#L96-L98

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}

theorem Light.Compiler.straight_newFrame (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i := by sorry
