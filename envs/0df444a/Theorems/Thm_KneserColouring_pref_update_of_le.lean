-- Prove2me | Theorems.Thm_KneserColouring_pref_update_of_le
-- name    : KneserColouring.pref_update_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:55.223036+00:00
-- url     : https://prove2.me/theorems/88ffe993-644e-5389-8700-76a0451aeb65
-- title:
--   Kneser Colouring: pref update of le
-- statement:
--   The Kneser Colouring construction uses the pref update of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L46-L55
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerParity.lean#L46-L55

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.pref_update_of_le {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} {c0 : Fin n}
    {v : SignType} {i : ℕ} (hi : i ≤ (ρ c0).val) :
    pref (Function.update t c0 v, ρ) i = pref (t, ρ) i := by sorry
