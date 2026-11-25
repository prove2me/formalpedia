-- Prove2me | Theorems.Thm_HiltonMilner_card_union_lt_of_mem
-- name    : HiltonMilner.card_union_lt_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:54:34.571292+00:00
-- url     : https://prove2.me/theorems/414dd6b6-d434-57d1-9226-864ee0c31d59
-- title:
--   Hilton Milner: card union lt of mem
-- statement:
--   The Hilton Milner construction uses the card union lt of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L91-L95
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean#L91-L95

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.card_union_lt_of_mem {A B X : Finset ℕ} {a z : ℕ} (hA : #A = a) (hB : #B = a)
    (hzA : z ∈ A) (hzB : z ∈ B) (hX : 2 * a ≤ #X) : #(A ∪ B) < #X := by sorry
