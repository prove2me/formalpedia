-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_op_mem_tri
-- name    : Kirkman.SteinerOp.op_mem_tri
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:11.990857+00:00
-- url     : https://prove2.me/theorems/4b2afa16-87f4-462b-a958-fc6ca5dec43a
-- title:
--   Steiner Op: op mem tri
-- statement:
--   The operation maps two points of a triple into the triple.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L72-L79
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L72-L79

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

theorem Kirkman.SteinerOp.op_mem_tri {a b u w : P} (hu : u ∈ S.tri a b) (hw : w ∈ S.tri a b) :
    S.op u w ∈ S.tri a b := by sorry
