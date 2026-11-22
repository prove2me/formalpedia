-- Prove2me | Theorems.Thm_GJKKL_card_filter_not_disjoint_le
-- name    : GJKKL.card_filter_not_disjoint_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:54.18373+00:00
-- url     : https://prove2.me/theorems/beb254b5-c9c0-4952-85f4-19ca927aac26
-- title:
--   GJKKL: card filter not disjoint le
-- statement:
--   The edges of `H` that meet a given set `f`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L86-L97
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Process.lean#L86-L97

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

theorem GJKKL.card_filter_not_disjoint_le (H : Finset (Finset V)) (f : Finset V) :
    (H.filter (fun e => ¬ Disjoint e f)).card ≤ ∑ v ∈ f, degree H v := by sorry
