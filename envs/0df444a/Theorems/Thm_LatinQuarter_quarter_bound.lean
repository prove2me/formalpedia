-- Prove2me | Theorems.Thm_LatinQuarter_quarter_bound
-- name    : LatinQuarter.quarter_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:06.536478+00:00
-- url     : https://prove2.me/theorems/4b83f16b-0395-46c9-98a3-ce5328d6f790
-- title:
--   Latin Quarter: quarter bound
-- statement:
--   A single statement giving the unrestricted lower bound and an
--   explicit critical set attaining it in the cyclic square.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L75-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L75-L81

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.quarter_bound (n : ℕ) (hn : 0 < n) :
    (∀ (L : Square n) (P : Finset (Cell n)),
      IsDefining P L → n * n / 4 ≤ P.card) ∧
    IsCritical (cornerSet n) (cyclic n) ∧
    (cornerSet n).card = n * n / 4 := by sorry
