-- Prove2me | Theorems.Thm_KneserColouring_supp_mono
-- name    : KneserColouring.supp_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:30.994791+00:00
-- url     : https://prove2.me/theorems/8a970805-fdf9-4f4f-a5de-9ac8fc48ac37
-- title:
--   Kneser Colouring: supp mono
-- statement:
--   The Kneser Colouring construction uses the supp mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L214-L218
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L214-L218

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

theorem KneserColouring.supp_mono : univ.filter (fun i => x i ≠ 0) ⊆ univ.filter (fun i => y i ≠ 0) := by sorry
