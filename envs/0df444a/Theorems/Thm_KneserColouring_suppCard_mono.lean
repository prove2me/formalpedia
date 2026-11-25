-- Prove2me | Theorems.Thm_KneserColouring_suppCard_mono
-- name    : KneserColouring.suppCard_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:37.00103+00:00
-- url     : https://prove2.me/theorems/bfa8796e-c9b6-5f60-bdf5-d054c1bed199
-- title:
--   Kneser Colouring: supp Card mono
-- statement:
--   The Kneser Colouring construction uses the supp Card mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L220-L220
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L220-L220

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
variable {x y : Fin n → SignType} (hxy : ∀ i, x i ≠ 0 → x i = y i)
include hxy

theorem KneserColouring.suppCard_mono : suppCard x ≤ suppCard y := by sorry
