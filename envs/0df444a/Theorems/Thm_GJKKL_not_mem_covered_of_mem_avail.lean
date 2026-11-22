-- Prove2me | Theorems.Thm_GJKKL_not_mem_covered_of_mem_avail
-- name    : GJKKL.not_mem_covered_of_mem_avail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:53:02.897059+00:00
-- url     : https://prove2.me/theorems/469967cc-395e-4099-a097-20108ece410c
-- title:
--   GJKKL: not mem covered of mem avail
-- statement:
--   The vertices of an available edge are uncovered.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L62-L64
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean#L62-L64

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
public import Definitions.Def_GJKKL_Trajectory_Increments
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.not_mem_covered_of_mem_avail {H : Finset (Finset V)} {h : List (Finset V)}
    {f : Finset V} (hf : f ∈ avail H h) {u : V} (hu : u ∈ f) : u ∉ covered h := by sorry
