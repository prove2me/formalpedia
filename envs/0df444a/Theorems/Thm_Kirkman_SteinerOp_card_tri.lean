-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_card_tri
-- name    : Kirkman.SteinerOp.card_tri
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:07.199837+00:00
-- url     : https://prove2.me/theorems/9740f207-c701-4652-be8a-2f3321f0fe0a
-- title:
--   Steiner Op: card tri
-- statement:
--   The Steiner Op construction uses the card tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L56-L60
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L56-L60

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

theorem Kirkman.SteinerOp.card_tri {x y : P} (h : x ≠ y) : #(S.tri x y) = 3 := by sorry
