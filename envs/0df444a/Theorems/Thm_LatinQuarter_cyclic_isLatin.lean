-- Prove2me | Theorems.Thm_LatinQuarter_cyclic_isLatin
-- name    : LatinQuarter.cyclic_isLatin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:52.621856+00:00
-- url     : https://prove2.me/theorems/4036747a-be10-4f15-9d3d-8c6b4983e542
-- title:
--   Latin Quarter: cyclic is Latin
-- statement:
--   The Latin Quarter construction uses the cyclic is Latin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L24-L26
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L24-L26

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

theorem LatinQuarter.cyclic_isLatin (n : ℕ) (hn : 0 < n) : IsLatin (cyclic n) := by sorry
