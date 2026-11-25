-- Prove2me | Theorems.Thm_KneserColouring_labSet_neg
-- name    : KneserColouring.labSet_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:18.945278+00:00
-- url     : https://prove2.me/theorems/59791e12-dc45-5a72-85a3-748c82265ff9
-- title:
--   Kneser Colouring: lab Set neg
-- statement:
--   The Kneser Colouring construction uses the lab Set neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L28-L35
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L28-L35

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets
public import Definitions.Def_KneserLib_TuckerRooms
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_TuckerMain
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n : ℕ}

theorem KneserColouring.labSet_neg (lab : (Fin n → SignType) → ℤ) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    {k : ℕ} {t : Fin n → SignType} {ρ : Equiv.Perm (Fin n)} (h : IsRoom k (t, ρ)) (hk : k ≤ n) :
    labSet lab k (-t, ρ) = (labSet lab k (t, ρ)).image (fun a => -a) := by sorry
