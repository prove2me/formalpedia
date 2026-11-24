-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_mem_tri_right
-- name    : Kirkman.SteinerOp.mem_tri_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:11.983064+00:00
-- url     : https://prove2.me/theorems/9613b1bd-ab66-41e2-9bf8-95bf578c58aa
-- title:
--   Steiner Op: mem tri right
-- statement:
--   The Steiner Op construction uses the mem tri right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L95-L95
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L95-L95

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
variable [DecidableEq P]

theorem Kirkman.SteinerOp.mem_tri_right (x y : P) : y ∈ S.tri x y := by sorry
