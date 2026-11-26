-- Prove2me | Theorems.Thm_HajnalSzemeredi_transfer
-- name    : HajnalSzemeredi.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:26.6583+00:00
-- url     : https://prove2.me/theorems/e065a448-9b57-494a-bd67-d83badc61ed1
-- title:
--   Hajnal Szemeredi: transfer
-- statement:
--   The Hajnal Szemeredi construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Reach.lean#L30-L37
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Reach.lean#L30-L37

module
public import Mathlib.Logic.Relation
public import Definitions.Def_HajnalSzemeredi_Reach
set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
open Relation
variable {α : Type*}

theorem HajnalSzemeredi.transfer {R R' : α → α → Prop} {x z : α} (h : ReflTransGen R x z)
    (hR : ∀ a b, R a b → b ≠ x → R' a b) : ReflTransGen R' x z := by sorry
