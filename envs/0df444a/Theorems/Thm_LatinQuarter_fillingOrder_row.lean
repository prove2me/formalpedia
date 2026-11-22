-- Prove2me | Theorems.Thm_LatinQuarter_fillingOrder_row
-- name    : LatinQuarter.fillingOrder_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:21:26.158149+00:00
-- url     : https://prove2.me/theorems/5703d12d-0173-473b-bf6e-16a5de84d11b
-- title:
--   Latin Quarter: filling Order row
-- statement:
--   The Latin Quarter construction uses the filling Order row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L40-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L40-L48

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

theorem LatinQuarter.fillingOrder_row {n : ℕ} (r i c d : Fin n) (hi : i < r) :
    fillingOrder i d < fillingOrder r c := by sorry
