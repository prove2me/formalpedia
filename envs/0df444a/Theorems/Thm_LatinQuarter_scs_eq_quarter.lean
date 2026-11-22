-- Prove2me | Theorems.Thm_LatinQuarter_scs_eq_quarter
-- name    : LatinQuarter.scs_eq_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:03.804746+00:00
-- url     : https://prove2.me/theorems/a8a46e58-922e-451e-9d35-a0005447bad6
-- title:
--   Latin Quarter: scs eq quarter
-- statement:
--   Main theorem: the least size over all Latin squares is `floor(n²/4)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L57-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L57-L62

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.scs_eq_quarter (n : ℕ) (hn : 0 < n) : scs n = n * n / 4 := by sorry
