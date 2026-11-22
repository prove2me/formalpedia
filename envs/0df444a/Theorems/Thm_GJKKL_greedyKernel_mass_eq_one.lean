-- Prove2me | Theorems.Thm_GJKKL_greedyKernel_mass_eq_one
-- name    : GJKKL.greedyKernel_mass_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:57.472594+00:00
-- url     : https://prove2.me/theorems/c50f6aa2-b41e-45a6-b6a3-9bd46deeb7bb
-- title:
--   GJKKL: greedy Kernel mass eq one
-- statement:
--   On a step with at least one available edge the kernel has total mass `1`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L147-L151
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L147-L151

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.greedyKernel_mass_eq_one {H : Finset (Finset V)} {h : List (Finset V)}
    (hne : (avail H h).Nonempty) : ∑ a, (greedyKernel H).K h a = 1 := by sorry
