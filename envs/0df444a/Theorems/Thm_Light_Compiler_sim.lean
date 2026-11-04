-- Prove2me | Theorems.Thm_Light_Compiler_sim
-- name    : Light.Compiler.sim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:21:16.375483+00:00
-- url     : https://prove2.me/theorems/f0315116-3d3e-4755-af5f-b0081bf9ceaf
-- title:
--   Compiler: sim
-- statement:
--   **The simulation theorem.**  The code of a statement matches every run of the statement.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Simulation.lean#L466-L477
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Simulation.lean#L466-L477

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} (S : Setting W)
variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}

theorem Light.Compiler.sim (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) :
    Simulates S d s σ σ' c := by sorry
