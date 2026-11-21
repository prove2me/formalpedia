-- Prove2me | Theorems.Thm_MinModulus_unshift_dsum_LeanPool_e110dec
-- name    : MinModulus.unshift_dsum_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:17.996968+00:00
-- url     : https://prove2.me/theorems/226e479e-ef49-497b-bcb2-895f0d0fb95a
-- title:
--   Min Modulus: unshift dsum Lean Pool e110dec
-- statement:
--   Peel index 0 off a digit sum (inverse of `shift_dsum`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L753-L765
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L753-L765

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

theorem MinModulus.unshift_dsum_LeanPool_e110dec (w : ℕ) (k : ℕ → ℕ) :
    dsum (w + 1) k = k 0 + dsum w (fun i => k (i + 1)) := by sorry
