-- Prove2me | Theorems.Thm_LatinQuarter_cornerSet_isDefining
-- name    : LatinQuarter.cornerSet_isDefining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:52.868336+00:00
-- url     : https://prove2.me/theorems/62dd84a4-fa03-4a6a-96b8-1d44092ed70f
-- title:
--   Latin Quarter: corner Set is Defining
-- statement:
--   The Latin Quarter construction uses the corner Set is Defining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L113-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L113-L126

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

theorem LatinQuarter.cornerSet_isDefining (n : ℕ) (hn : 0 < n) :
    IsDefining (cornerSet n) (cyclic n) := by sorry
