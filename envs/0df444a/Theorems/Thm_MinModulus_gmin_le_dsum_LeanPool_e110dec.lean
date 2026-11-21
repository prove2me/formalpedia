-- Prove2me | Theorems.Thm_MinModulus_gmin_le_dsum_LeanPool_e110dec
-- name    : MinModulus.gmin_le_dsum_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:15.052518+00:00
-- url     : https://prove2.me/theorems/a5c3dc6c-e92d-4995-96cc-a8c3b9a4e008
-- title:
--   Min Modulus: gmin le dsum Lean Pool e110dec
-- statement:
--   **Greedy minimality** (paper Lemma 3, downward half): the digit sum of any
--   representation is at least the greedy digit sum of its value.  Induction on
--   the width: split the bottom coin `k 0 = M % 2 + 2t`; the `2t` surplus carries
--   up into the shifted representation, and `gmin_add_le_LeanPool_e110dec` absorbs it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L785-L803
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L785-L803

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums
set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset

theorem MinModulus.gmin_le_dsum_LeanPool_e110dec : ∀ w (k : ℕ → ℕ), gmin w (val (w + 1) k) ≤ dsum (w + 1) k := by sorry
