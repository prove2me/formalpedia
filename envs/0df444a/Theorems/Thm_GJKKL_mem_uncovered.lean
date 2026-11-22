-- Prove2me | Theorems.Thm_GJKKL_mem_uncovered
-- name    : GJKKL.mem_uncovered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:54.489963+00:00
-- url     : https://prove2.me/theorems/0e7157c5-5c2e-4f74-af20-fee67a78028e
-- title:
--   GJKKL: mem uncovered
-- statement:
--   The GJKKL construction uses the mem uncovered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L102-L103
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean#L102-L103

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.mem_uncovered {h : List (Finset V)} {v : V} : v ∈ uncovered h ↔ v ∉ covered h := by sorry
