-- Prove2me | Theorems.Thm_MinModulus_theoremA
-- name    : MinModulus.theoremA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:23.249478+00:00
-- url     : https://prove2.me/theorems/17836f2f-47c6-4f4f-9928-c117e65ebf40
-- title:
--   Min Modulus: theorem A
-- statement:
--   **Theorem A** (upper bound, paper §5): the super-increasing set is valid at
--   `N = 2^n − 2^⌊log₂ n⌋`.  Pass to `M = val n k ≡ 2^n − 1 [MOD N]` and split:
--   `M < 2^n − 1` falls below the floor (`2^m ≤ n` — the only place `⌊log₂⌋`
--   enters); `M = 2^n − 1` is `ones_unique_LeanPool_e110dec`; and `M = 2^n − 1 + jN` has greedy
--   digit sum at least `n + j > n` by `slack_LeanPool_e110dec` — uniformly in `j ≥ 1` and `n ≥ 2`,
--   with no range restriction and no small-`n` cases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L854-L931
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L854-L931

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

theorem MinModulus.theoremA {n : ℕ} (hn : 2 ≤ n) :
    Valid n (2 ^ n - 2 ^ Nat.log 2 n) := by sorry
