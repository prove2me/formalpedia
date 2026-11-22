-- Prove2me | Theorems.Thm_GJKKL_weight_cons_of_mem
-- name    : GJKKL.weight_cons_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:59.60301+00:00
-- url     : https://prove2.me/theorems/3ec73d5b-ded6-463d-9ec0-ec58afbf6cc7
-- title:
--   GJKKL: weight cons of mem
-- statement:
--   The GJKKL construction uses the weight cons of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L163-L166
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L163-L166

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

theorem GJKKL.weight_cons_of_mem {H : Finset (Finset V)} {a : Finset V} {h : List (Finset V)}
    (ha : a ∈ avail H h) :
    weight (greedyKernel H) (a :: h) = weight (greedyKernel H) h / (avail H h).card := by sorry
