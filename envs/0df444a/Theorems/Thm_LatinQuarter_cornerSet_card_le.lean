-- Prove2me | Theorems.Thm_LatinQuarter_cornerSet_card_le
-- name    : LatinQuarter.cornerSet_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:34.682327+00:00
-- url     : https://prove2.me/theorems/ef7d2839-ae5a-48f7-80c7-278d0ce57dd6
-- title:
--   Latin Quarter: corner Set card le
-- statement:
--   Fold the two corner triangles into a rectangle with `n/2` rows and
--   `n-n/2` columns. Their images lie on opposite sides of its anti-diagonal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/CornerSize.lean#L21-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/CornerSize.lean#L21-L59

module
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
public import Definitions.Def_LeanPool_LatinQuarter_Budget
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.cornerSet_card_le (n : ℕ) : (cornerSet n).card ≤ n * n / 4 := by sorry
