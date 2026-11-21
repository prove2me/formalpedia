-- Prove2me | Theorems.Thm_MinModulus_nmin_eq_LeanPool_e110dec
-- name    : MinModulus.nmin_eq_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:34.462184+00:00
-- url     : https://prove2.me/theorems/cce9aa5b-056e-4bc8-8114-079c530e464c
-- title:
--   Min Modulus: nmin eq Lean Pool e110dec
-- statement:
--   **Main theorem**: `Nmin(n) = 2^n − 2^⌊log₂ n⌋` — it is valid there, and
--   every smaller modulus (≥ 2) is invalid.  (Modulo `theoremA`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L935-L958
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L935-L958

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

theorem MinModulus.nmin_eq_LeanPool_e110dec {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {N | 2 ≤ N ∧ Valid n N} (2 ^ n - 2 ^ Nat.log 2 n) := by sorry
