-- Prove2me | Theorems.Thm_KneserColouring_image_erase_eq_of_dup
-- name    : KneserColouring.image_erase_eq_of_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:27.915955+00:00
-- url     : https://prove2.me/theorems/9bd5bcdb-11ac-4011-8bcc-f38ea1c0dd3a
-- title:
--   Kneser Colouring: image erase eq of dup
-- statement:
--   The Kneser Colouring construction uses the image erase eq of dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L179-L187
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/AltSets.lean#L179-L187

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset

theorem KneserColouring.image_erase_eq_of_dup {α : Type*} [DecidableEq α] {s : Finset α} {ℓ : α → ℤ} {j j' : α}
    (hj' : j' ∈ s) (hne : j' ≠ j) (heq : ℓ j' = ℓ j) : (s.erase j).image ℓ = s.image ℓ := by sorry
