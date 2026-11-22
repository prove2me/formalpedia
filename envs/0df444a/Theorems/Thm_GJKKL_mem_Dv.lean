-- Prove2me | Theorems.Thm_GJKKL_mem_Dv
-- name    : GJKKL.mem_Dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:21.481886+00:00
-- url     : https://prove2.me/theorems/c3abf5dc-4df7-4218-b41f-abc5f9d0133c
-- title:
--   GJKKL: mem Dv
-- statement:
--   The GJKKL construction uses the mem Dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L40-L42
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L40-L42

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.mem_Dv {H : Finset (Finset V)} {h : List (Finset V)} {v : V} {e : Finset V} :
    e ∈ Dv H h v ↔ e ∈ avail H h ∧ v ∈ e := by sorry
