-- Prove2me | Theorems.Thm_HiltonMilner_card_low_add_high
-- name    : HiltonMilner.card_low_add_high
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:01.25761+00:00
-- url     : https://prove2.me/theorems/0170f22e-cda6-571c-a4c0-768feb807323
-- title:
--   Hilton Milner: card low add high
-- statement:
--   The Hilton Milner construction uses the card low add high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L50-L59
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L50-L59

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_low_add_high (z : ℕ) (𝒜 : Finset (Finset ℕ)) :
    #𝒜 = #(low z 𝒜) + #(high z 𝒜) := by sorry
