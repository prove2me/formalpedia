-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_isSTSOn_triples
-- name    : Kirkman.SteinerOp.isSTSOn_triples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:08.378378+00:00
-- url     : https://prove2.me/theorems/7aa26714-1084-4f85-8566-7a1504ea57c1
-- title:
--   Steiner Op: is STSOn triples
-- statement:
--   The Steiner Op construction uses the is STSOn triples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L103-L111
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L103-L111

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
variable [Fintype P]

theorem Kirkman.SteinerOp.isSTSOn_triples : IsSTSOn S.triples := by sorry
