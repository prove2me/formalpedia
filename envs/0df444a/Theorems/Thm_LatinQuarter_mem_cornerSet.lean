-- Prove2me | Theorems.Thm_LatinQuarter_mem_cornerSet
-- name    : LatinQuarter.mem_cornerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:53.631325+00:00
-- url     : https://prove2.me/theorems/adb2f153-92d4-42aa-a54e-91f6ad64410f
-- title:
--   Latin Quarter: mem corner Set
-- statement:
--   The Latin Quarter construction uses the mem corner Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L33-L35
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Cyclic.lean#L33-L35

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

theorem LatinQuarter.mem_cornerSet {n : ℕ} (r c : Fin n) :
    (r, c) ∈ cornerSet n ↔ r.val + c.val < n / 2 ∨
      n + n / 2 ≤ r.val + c.val := by sorry
