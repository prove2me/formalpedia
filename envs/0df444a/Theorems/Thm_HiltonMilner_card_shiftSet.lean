-- Prove2me | Theorems.Thm_HiltonMilner_card_shiftSet
-- name    : HiltonMilner.card_shiftSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:43.930675+00:00
-- url     : https://prove2.me/theorems/79ea06c3-8c67-479c-889e-14b628067f3a
-- title:
--   Hilton Milner: card shift Set
-- statement:
--   The Hilton Milner construction uses the card shift Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L104-L110
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L104-L110

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_shiftSet (y z : ℕ) (A : Finset ℕ) : #(shiftSet y z A) = #A := by sorry
