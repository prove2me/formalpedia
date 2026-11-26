-- Prove2me | Theorems.Thm_HajnalSzemeredi_exists_step_avoid
-- name    : HajnalSzemeredi.exists_step_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:03.932273+00:00
-- url     : https://prove2.me/theorems/f31e9a5b-9e22-4054-a1ab-e95fbdce6061
-- title:
--   Hajnal Szemeredi: exists step avoid
-- statement:
--   The Hajnal Szemeredi construction uses the exists step avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Reach.lean#L39-L48
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Reach.lean#L39-L48

module
public import Mathlib.Logic.Relation
public import Definitions.Def_HajnalSzemeredi_Reach
set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
open Relation
variable {α : Type*}

theorem HajnalSzemeredi.exists_step_avoid {R : α → α → Prop} {x z : α} (h : ReflTransGen R x z) (hxz : x ≠ z) :
    ∃ j, R x j ∧ j ≠ x ∧ ReflTransGen (fun a b => R a b ∧ a ≠ x ∧ b ≠ x) j z := by sorry
