-- Prove2me | Theorems.Thm_KneserColouring_kLab_ne_zero_and_le
-- name    : KneserColouring.kLab_ne_zero_and_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:06.702273+00:00
-- url     : https://prove2.me/theorems/b5dfacad-7270-4554-a94f-9764811802de
-- title:
--   Kneser Colouring: k Lab ne zero and le
-- statement:
--   The Kneser Colouring construction uses the k Lab ne zero and le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L255-L272
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L255-L272

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerParity
public import Definitions.Def_KneserLib_KneserLabel
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
variable {n k q : ℕ}

theorem KneserColouring.kLab_ne_zero_and_le (c : {s : Finset (Fin n) // s.card = k} → Fin q) (hk : 0 < k)
    {x : Fin n → SignType} (hx : x ≠ 0) :
    kLab c x ≠ 0 ∧ |kLab c x| ≤ ((2 * k - 2 + q : ℕ) : ℤ) := by sorry
