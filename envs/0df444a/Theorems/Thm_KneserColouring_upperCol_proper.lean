-- Prove2me | Theorems.Thm_KneserColouring_upperCol_proper
-- name    : KneserColouring.upperCol_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:26.39848+00:00
-- url     : https://prove2.me/theorems/d8870aef-e66f-4e0d-9f7b-eed8dc8388b1
-- title:
--   Kneser Colouring: upper Col proper
-- statement:
--   The Kneser Colouring construction uses the upper Col proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L35-L72
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/KneserLabel.lean#L35-L72

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

theorem KneserColouring.upperCol_proper (hk : 0 < k) (hn : 2 * k ≤ n) (s t : {s : Finset (Fin n) // s.card = k})
    (hd : Disjoint s.1 t.1) : upperCol hk s ≠ upperCol hk t := by sorry
