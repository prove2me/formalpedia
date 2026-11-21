-- Prove2me | Theorems.Thm_MinModulus_gmin_step_LeanPool_e110dec
-- name    : MinModulus.gmin_step_LeanPool_e110dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:28.221385+00:00
-- url     : https://prove2.me/theorems/f9e6057b-2b83-432e-9a68-8cbf5b3829bc
-- title:
--   Min Modulus: gmin step Lean Pool e110dec
-- statement:
--   **Step lemma** (paper §5, Lemma 4): adding `2^{w+1} − 2^t` (`t ≤ w`;
--   subtraction encoded as `M' + 2^t = M + 2^{w+1}`) raises the greedy digit sum
--   by at least `1`.  Induction on `w`, peeling one bit: for `t ≥ 1` both sides
--   keep their parity and the shifted instance is `(w−1, t−1)`; for `t = 0` the
--   parity flips, and the odd-`M` branch pays two top coins via `gmin_add_pow_LeanPool_e110dec`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L681-L716
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MinModulusUniqueMultisetSum/UniqueSums.lean#L681-L716

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

theorem MinModulus.gmin_step_LeanPool_e110dec : ∀ w t M M', t ≤ w → M' + 2 ^ t = M + 2 ^ (w + 1) →
    gmin w M + 1 ≤ gmin w M' := by sorry
