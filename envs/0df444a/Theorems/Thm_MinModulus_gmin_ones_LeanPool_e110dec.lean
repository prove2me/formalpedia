-- Prove2me | Theorems.Thm_MinModulus_gmin_ones_LeanPool_e110dec
-- name    : MinModulus.gmin_ones_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:12.478049+00:00
-- url     : https://prove2.me/theorems/ff1f2e2b-e6ff-4cb7-a3e2-8712cccf99b0
-- title:
--   Min Modulus: gmin ones Lean Pool e110dec
-- statement:
--   Greedy digit sum of the all-ones target: `gmin w (2^{w+1} − 1) = w + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L663-L674
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L663-L674

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

theorem MinModulus.gmin_ones_LeanPool_e110dec : ∀ w, gmin w (2 ^ (w + 1) - 1) = w + 1 := by sorry
