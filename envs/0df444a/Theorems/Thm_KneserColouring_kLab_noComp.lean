-- Prove2me | Theorems.Thm_KneserColouring_kLab_noComp
-- name    : KneserColouring.kLab_noComp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:09.141456+00:00
-- url     : https://prove2.me/theorems/7b3c4840-3452-41b4-977f-bbb5a36c36a6
-- title:
--   Kneser Colouring: k Lab no Comp
-- statement:
--   The Kneser Colouring construction uses the k Lab no Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L307-L341
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L307-L341

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

theorem KneserColouring.kLab_noComp (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {x y : Fin n → SignType} (hx : x ≠ 0) (hxy : ∀ i, x i ≠ 0 → x i = y i) :
    kLab c x ≠ -kLab c y := by sorry
