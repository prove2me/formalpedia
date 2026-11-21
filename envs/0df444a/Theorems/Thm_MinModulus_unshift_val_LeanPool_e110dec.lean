-- Prove2me | Theorems.Thm_MinModulus_unshift_val_LeanPool_e110dec
-- name    : MinModulus.unshift_val_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:15.728918+00:00
-- url     : https://prove2.me/theorems/c72e28cd-d511-43a8-b125-90b5f6197733
-- title:
--   Min Modulus: unshift val Lean Pool e110dec
-- statement:
--   Peel index 0 off a value (inverse of `shift_val`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L738-L750
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L738-L750

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

theorem MinModulus.unshift_val_LeanPool_e110dec (w : ℕ) (k : ℕ → ℕ) :
    val (w + 1) k = k 0 + 2 * val w (fun i => k (i + 1)) := by sorry
