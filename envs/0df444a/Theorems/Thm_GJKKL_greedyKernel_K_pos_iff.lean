-- Prove2me | Theorems.Thm_GJKKL_greedyKernel_K_pos_iff
-- name    : GJKKL.greedyKernel_K_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:18.432847+00:00
-- url     : https://prove2.me/theorems/07d2bd3e-bc33-401c-8ae9-40b9b3c0579b
-- title:
--   GJKKL: greedy Kernel K pos iff
-- statement:
--   The GJKKL construction uses the greedy Kernel K pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L133-L144
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L133-L144

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

theorem GJKKL.greedyKernel_K_pos_iff {H : Finset (Finset V)} {h : List (Finset V)} {a : Finset V} :
    0 < (greedyKernel H).K h a ↔ a ∈ avail H h := by sorry
