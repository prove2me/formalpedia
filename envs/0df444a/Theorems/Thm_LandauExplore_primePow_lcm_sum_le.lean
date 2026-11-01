-- Prove2me | Theorems.Thm_LandauExplore_primePow_lcm_sum_le
-- name    : LandauExplore.primePow_lcm_sum_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T23:55:22.506794+00:00
-- url     : https://prove2.me/theorems/4a3b566e-cd40-4270-a67f-ce4bd1c333fa
-- title:
--   Prime-power parts of a least common multiple sum to at most the sum of the set
-- statement:
--   For any finite set $s$ of positive natural numbers, the sum of the prime-power parts of their least common multiple is at most the sum of the elements of $s$. That is, if $L$ is the least common multiple of $s$, then $\sum_{p \mid L} p^{v_p(L)} \le \sum_{a \in s} a$, where $v_p(L)$ is the exponent of the prime $p$ in $L$. Replacing a family of integers by the prime powers dividing their least common multiple therefore does not increase the total sum. This is the arithmetic core of the prime-power characterization of permutation orders used in the analysis of Landau's function.
-- source:
--   Newly formalized lemma for the Landau-function route (prime-power maximiser step); classical background in Deléglise–Nicolas, 'The Landau function and the Riemann hypothesis', arXiv:1907.07664

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
open Finset

namespace LandauExplore
theorem primePow_lcm_sum_le (s : Finset ℕ) (hs : ∀ a ∈ s, a ≠ 0) : ∑ p ∈ (s.lcm id).primeFactors, p ^ (s.lcm id).factorization p ≤ ∑ a ∈ s, a := by sorry
end LandauExplore
