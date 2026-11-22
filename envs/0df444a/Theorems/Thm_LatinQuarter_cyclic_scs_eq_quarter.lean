-- Prove2me | Theorems.Thm_LatinQuarter_cyclic_scs_eq_quarter
-- name    : LatinQuarter.cyclic_scs_eq_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:12.696289+00:00
-- url     : https://prove2.me/theorems/f0dd739b-19bd-4a4d-8d32-0cae4528ece2
-- title:
--   Latin Quarter: cyclic scs eq quarter
-- statement:
--   The cyclic Latin square attains the same least size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L65-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Main.lean#L65-L71

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.cyclic_scs_eq_quarter (n : ℕ) (hn : 0 < n) :
    scsOf (cyclic n) = n * n / 4 := by sorry
