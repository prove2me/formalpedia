-- Prove2me | Theorems.Thm_LatinQuarter_cornerSet_card
-- name    : LatinQuarter.cornerSet_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:04.812949+00:00
-- url     : https://prove2.me/theorems/142585a9-0cc7-4db0-ba8b-938a9f6ed468
-- title:
--   Latin Quarter: corner Set card
-- statement:
--   The Latin Quarter construction uses the corner Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L32-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L32-L35

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.cornerSet_card (n : ℕ) (hn : 0 < n) :
    (cornerSet n).card = n * n / 4 := by sorry
