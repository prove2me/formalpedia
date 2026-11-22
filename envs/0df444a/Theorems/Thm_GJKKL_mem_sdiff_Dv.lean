-- Prove2me | Theorems.Thm_GJKKL_mem_sdiff_Dv
-- name    : GJKKL.mem_sdiff_Dv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:34.003389+00:00
-- url     : https://prove2.me/theorems/9eff40f1-c04f-450c-a080-0b0f13780444
-- title:
--   GJKKL: mem sdiff Dv
-- statement:
--   The GJKKL construction uses the mem sdiff Dv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L64-L66
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean#L64-L66

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.mem_sdiff_Dv {H : Finset (Finset V)} {h : List (Finset V)} {v : V} {a : Finset V} :
    a ∈ avail H h \ Dv H h v ↔ a ∈ avail H h ∧ v ∉ a := by sorry
