-- Prove2me | Theorems.Thm_GJKKL_avail_cons
-- name    : GJKKL.avail_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:39.18881+00:00
-- url     : https://prove2.me/theorems/e2608024-2215-4ee2-85fe-0f89e187775a
-- title:
--   GJKKL: avail cons
-- statement:
--   The GJKKL construction uses the avail cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L54-L58
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L54-L58

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

theorem GJKKL.avail_cons (H : Finset (Finset V)) (a : Finset V) (h : List (Finset V)) :
    avail H (a :: h) = (avail H h).filter (fun e => Disjoint e a) := by sorry
