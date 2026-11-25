-- Prove2me | Theorems.Thm_KneserColouring_even_card_of_involution
-- name    : KneserColouring.even_card_of_involution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:05.322271+00:00
-- url     : https://prove2.me/theorems/570db531-b98b-5073-83b5-625a52939a4f
-- title:
--   Kneser Colouring: even card of involution
-- statement:
--   A finset carrying a fixed-point-free involution has even cardinality.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L37-L44
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L37-L44

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.even_card_of_involution {α : Type*} (s : Finset α) (g : α → α)
    (hg_mem : ∀ a ∈ s, g a ∈ s) (hne : ∀ a ∈ s, g a ≠ a) (hinv : ∀ a ∈ s, g (g a) = a) :
    Even s.card := by sorry
