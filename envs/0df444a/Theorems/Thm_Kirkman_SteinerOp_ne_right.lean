-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_ne_right
-- name    : Kirkman.SteinerOp.ne_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:05.382175+00:00
-- url     : https://prove2.me/theorems/8334d3af-cf92-4d99-925e-5a509a24c09e
-- title:
--   Steiner Op: ne right
-- statement:
--   The Steiner Op construction uses the ne right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L48-L49
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L48-L49

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

theorem Kirkman.SteinerOp.ne_right {x y : P} (h : x ≠ y) : S.op x y ≠ y := by sorry
