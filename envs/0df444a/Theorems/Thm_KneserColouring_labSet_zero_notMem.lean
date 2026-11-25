-- Prove2me | Theorems.Thm_KneserColouring_labSet_zero_notMem
-- name    : KneserColouring.labSet_zero_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:00.811534+00:00
-- url     : https://prove2.me/theorems/6f76d0ad-28f9-4cba-b289-1920ed8bf6bc
-- title:
--   Kneser Colouring: lab Set zero not Mem
-- statement:
--   The Kneser Colouring construction uses the lab Set zero not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L42-L46
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L42-L46

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

theorem KneserColouring.labSet_zero_notMem {lab : (Fin n → SignType) → ℤ} (hNC : NoCompLab lab) {k : ℕ}
    {r : Room n} (h : IsRoom k r) (hk : k ≤ n) : (0 : ℤ) ∉ labSet lab k r := by sorry
