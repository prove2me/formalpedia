-- Prove2me | Theorems.Thm_KneserColouring_abs_kLab_small
-- name    : KneserColouring.abs_kLab_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:55.027906+00:00
-- url     : https://prove2.me/theorems/e44b0953-c99b-5d23-b4c4-f7d0fd3ead7a
-- title:
--   Kneser Colouring: abs k Lab small
-- statement:
--   The Kneser Colouring construction uses the abs k Lab small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L235-L239
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L235-L239

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

theorem KneserColouring.abs_kLab_small (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    {x : Fin n → SignType} (hx : suppCard x ≤ 2 * k - 2) : |kLab c x| = suppCard x := by sorry
