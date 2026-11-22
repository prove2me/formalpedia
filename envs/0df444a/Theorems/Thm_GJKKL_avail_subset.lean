-- Prove2me | Theorems.Thm_GJKKL_avail_subset
-- name    : GJKKL.avail_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:26.803833+00:00
-- url     : https://prove2.me/theorems/79bb1d17-3f8f-4563-9fd8-48fd740ff2e2
-- title:
--   GJKKL: avail subset
-- statement:
--   The GJKKL construction uses the avail subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L64-L65
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L64-L65

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

theorem GJKKL.avail_subset (H : Finset (Finset V)) (h : List (Finset V)) : avail H h ⊆ H := by sorry
