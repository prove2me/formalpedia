-- Prove2me | Theorems.Thm_KneserTheorem_lovasz_kneser
-- name    : KneserTheorem.lovasz_kneser
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:06:58.938506+00:00
-- url     : https://prove2.me/theorems/a1ff04c5-5487-47b0-a758-beb730ed82ba
-- title:
--   Kneser Theorem: lovasz kneser
-- statement:
--   **Lovász's theorem (Kneser's conjecture).** For `0 < k ≤ n / 2`, the Kneser graph `KG(n, k)`
--   has chromatic number exactly `n − 2k + 2`.
--
--   Source: https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/Solution.lean#L45-L48
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/Solution.lean#L45-L48

module
public import Mathlib
public import Definitions.Def_KneserLib_Kneser
public import Definitions.Def_KneserLovasz_Solution
public import Theorems.Thm_KneserColouring_lovasz_kneser

set_option autoImplicit true
@[expose] public section
public section
open KneserTheorem

theorem KneserTheorem.lovasz_kneser {n k : ℕ} (hk : 0 < k) (hn : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 2) ∧
      ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by sorry
