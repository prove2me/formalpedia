-- Prove2me | Theorems.Thm_HiltonMilner_card_sh
-- name    : HiltonMilner.card_sh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:55.369856+00:00
-- url     : https://prove2.me/theorems/4c533a3a-b6ca-5b3a-8da8-be7512435341
-- title:
--   Hilton Milner: card sh
-- statement:
--   The Hilton Milner construction uses the card sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L71-L72
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L71-L72

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_sh (y z : ℕ) (𝒜 : Finset (Finset ℕ)) : #(sh y z 𝒜) = #𝒜 := by sorry
