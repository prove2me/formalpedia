-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_ne_left
-- name    : Kirkman.SteinerOp.ne_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:15.369457+00:00
-- url     : https://prove2.me/theorems/63b79384-e66e-4af6-a878-a1b639f2b0db
-- title:
--   Steiner Op: ne left
-- statement:
--   The Steiner Op construction uses the ne left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L42-L46
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L42-L46

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

theorem Kirkman.SteinerOp.ne_left {x y : P} (h : x ≠ y) : S.op x y ≠ x := by sorry
