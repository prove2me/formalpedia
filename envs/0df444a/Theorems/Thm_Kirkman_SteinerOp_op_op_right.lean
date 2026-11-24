-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_op_op_right
-- name    : Kirkman.SteinerOp.op_op_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:14.551699+00:00
-- url     : https://prove2.me/theorems/ed09e03d-e9f3-4ae0-9552-b3e0256bd6dc
-- title:
--   Steiner Op: op op right
-- statement:
--   The Steiner Op construction uses the op op right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L66-L66
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L66-L66

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

theorem Kirkman.SteinerOp.op_op_right (x y : P) : S.op y (S.op x y) = x := by sorry
