-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_op_op_left
-- name    : Kirkman.SteinerOp.op_op_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:17.206566+00:00
-- url     : https://prove2.me/theorems/5b807f54-63a6-4faa-99c2-44e0882ca27f
-- title:
--   Steiner Op: op op left
-- statement:
--   The Steiner Op construction uses the op op left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L63-L63
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L63-L63

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
omit [DecidableEq P]

theorem Kirkman.SteinerOp.op_op_left (x y : P) : S.op (S.op x y) x = y := by sorry
