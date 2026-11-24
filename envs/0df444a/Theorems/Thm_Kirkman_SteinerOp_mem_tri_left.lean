-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_mem_tri_left
-- name    : Kirkman.SteinerOp.mem_tri_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:21.184497+00:00
-- url     : https://prove2.me/theorems/67ae04c7-d594-45d4-8039-2c8a77935362
-- title:
--   Steiner Op: mem tri left
-- statement:
--   The Steiner Op construction uses the mem tri left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L93-L93
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L93-L93

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

theorem Kirkman.SteinerOp.mem_tri_left (x y : P) : x ∈ S.tri x y := by sorry
