-- Prove2me | Theorems.Thm_KneserColouring_kLab_neg
-- name    : KneserColouring.kLab_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:50.671075+00:00
-- url     : https://prove2.me/theorems/e43b8e96-2129-5253-b23f-3738b0e3b382
-- title:
--   Kneser Colouring: k Lab neg
-- statement:
--   The Kneser Colouring construction uses the k Lab neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L274-L305
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L274-L305

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

theorem KneserColouring.kLab_neg (c : {s : Finset (Fin n) // s.card = k} → Fin q)
    (hc : ∀ s t, s ≠ t → Disjoint s.1 t.1 → c s ≠ c t) (hk : 0 < k)
    {x : Fin n → SignType} (hx : x ≠ 0) : kLab c (-x) = -kLab c x := by sorry
