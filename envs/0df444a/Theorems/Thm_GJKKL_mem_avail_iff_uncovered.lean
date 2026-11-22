-- Prove2me | Theorems.Thm_GJKKL_mem_avail_iff_uncovered
-- name    : GJKKL.mem_avail_iff_uncovered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:26.056779+00:00
-- url     : https://prove2.me/theorems/26d40c17-93df-4fa2-8a76-80ad3b8cd536
-- title:
--   GJKKL: mem avail iff uncovered
-- statement:
--   The GJKKL construction uses the mem avail iff uncovered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L73-L83
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L73-L83

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

theorem GJKKL.mem_avail_iff_uncovered {H : Finset (Finset V)} {h : List (Finset V)} {e : Finset V} :
    e ∈ avail H h ↔ e ∈ H ∧ Disjoint e (covered h) := by sorry
