-- Prove2me | Theorems.Thm_Nat_alternating_choose_convolution
-- name    : Nat.alternating_choose_convolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:26:05.254961+00:00
-- url     : https://prove2.me/theorems/146e1b94-1568-4db2-98b8-6c12a146ed2e
-- title:
--   Alternating binomial convolution coefficient over a commutative ring
-- statement:
--   For any commutative ring R and natural numbers n,m,
--
--   $$\sum_{k=0}^{n}\binom{n}{k}(-1)^k\binom{k}{m}=\begin{cases}(-1)^n,&m=n,\\0,&m\ne n.\end{cases}$$
--
--   The identity includes m>n, n=0 and rings of positive characteristic. It is the coefficient cancellation underlying finite binomial inversion.
-- source:
--   Derived coefficient identity from Nat.choose_mul and Int.alternating_sum_range_choose in pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/Data/Nat/Choose/Basic.lean and Sum.lean: https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Choose. This commutative-ring coefficient formulation is a derived lemma, rather than a quoted source theorem.

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

open Finset

theorem Nat.alternating_choose_convolution {R : Type*} [CommRing R] (n m : ℕ) :
    (∑ k ∈ range (n + 1), (n.choose k : R) * (-1 : R)^k * (k.choose m : R)) =
      if m = n then (-1 : R)^n else 0 := by sorry
