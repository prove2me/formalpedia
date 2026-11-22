-- Prove2me | Theorems.Thm_LatinQuarter_fillingOrder_column
-- name    : LatinQuarter.fillingOrder_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:29.61133+00:00
-- url     : https://prove2.me/theorems/80a53590-82c4-4cb2-8dc2-920ffa2147a1
-- title:
--   Latin Quarter: filling Order column
-- statement:
--   The Latin Quarter construction uses the filling Order column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L50-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L50-L55

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter

theorem LatinQuarter.fillingOrder_column {n : ℕ} (r c j : Fin n) (hj : c < j) :
    fillingOrder r j < fillingOrder r c := by sorry
