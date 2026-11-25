-- Prove2me | Theorems.Thm_KneserColouring_tucker_core
-- name    : KneserColouring.tucker_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:41.168937+00:00
-- url     : https://prove2.me/theorems/a795cc69-fb73-558c-bc9d-466bd2c57597
-- title:
--   Kneser Colouring: tucker core
-- statement:
--   The core of the octahedral Tucker lemma: without complementary pairs, `n ≤ m`.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L211-L241
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/TuckerMain.lean#L211-L241

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

theorem KneserColouring.tucker_core {m : ℕ} (lab : (Fin n → SignType) → ℤ)
    (hlab : ∀ x, x ≠ 0 → |lab x| ≤ m) (hanti : ∀ x, x ≠ 0 → lab (-x) = -lab x)
    (hNC : NoCompLab lab) (hn : 1 ≤ n) : n ≤ m := by sorry
