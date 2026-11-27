-- Prove2me | Theorems.Thm_NativeOnePass_copy_replay_exact
-- name    : NativeOnePass.copy_replay_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T02:29:00.136164+00:00
-- url     : https://prove2.me/theorems/6b97bd4d-40ea-4f14-8a6e-7dabe7a43e14
-- title:
--   Any native binary-input machine has an exact one-pass simulation
-- statement:
--   For any native multitape description, the compiled description adds one work tape. On any binary input x its output and halting flag after t+2|x|+3 transitions are exactly those of the source after t transitions. Its physical input-head position never decreases in a step.
-- source:
--   Copy-and-replay construction in the Complexitylib universal multitape model.

import Definitions.Def_NativeOnePassCompiler

open Turing.MultiTapeTM.Universal NativeOnePass

theorem NativeOnePass.copy_replay_exact (d : Desc) :
    (onePassDesc d).tapes = d.tapes+1 ∧
    (∀ (x : List Bool) (t : ℕ), simulate (onePassDesc d) (x.map Bool.toNat) (t+(2*x.length+3)) =
      simulate d (x.map Bool.toNat) t) ∧
    (∀ (x : List ℕ) (c : SCfg), c.inputPos ≤ (step (onePassDesc d) x c).1.inputPos) := by sorry
