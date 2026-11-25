-- Prove2me | Theorems.Thm_KneserColouring_lovasz_kneser
-- name    : KneserColouring.lovasz_kneser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:00.483429+00:00
-- url     : https://prove2.me/theorems/b4594a0c-3cb7-53f0-b6b3-609a781818b2
-- title:
--   Kneser Colouring: lovasz kneser
-- statement:
--   **Lovász's theorem (Kneser's conjecture).** For `0 < k ≤ n / 2`, the Kneser graph `KG(n, k)`
--   has chromatic number exactly `n − 2k + 2`.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/Kneser.lean#L50-L62
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/KneserLib/Kneser.lean#L50-L62

module
public import Mathlib
public import Definitions.Def_KneserLib_TuckerMain
public import Definitions.Def_KneserLib_KneserLabel
public import Definitions.Def_KneserLib_Kneser
set_option autoImplicit true
@[expose] public section
public section
open KneserColouring

theorem KneserColouring.lovasz_kneser {n k : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) ∧
      ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by sorry
