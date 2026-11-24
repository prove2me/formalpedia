-- Prove2me | Theorems.Thm_Kirkman_SteinerOp_tri_eq
-- name    : Kirkman.SteinerOp.tri_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:17.663048+00:00
-- url     : https://prove2.me/theorems/66441d7a-145c-48c3-be61-6505da08f140
-- title:
--   Steiner Op: tri eq
-- statement:
--   The Steiner Op construction uses the tri eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L81-L91
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L81-L91

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

theorem Kirkman.SteinerOp.tri_eq {a b x y : P} (hab : a ≠ b) (hxy : x ≠ y) (hx : x ∈ S.tri a b)
    (hy : y ∈ S.tri a b) : S.tri a b = S.tri x y := by sorry
