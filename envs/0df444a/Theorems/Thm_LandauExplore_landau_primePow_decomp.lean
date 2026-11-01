-- Prove2me | Theorems.Thm_LandauExplore_landau_primePow_decomp
-- name    : LandauExplore.landau_primePow_decomp
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:30:48.381364+00:00
-- url     : https://prove2.me/theorems/83734d16-cf30-4135-a05d-fdfe68fec5f0
-- title:
--   Landau maximiser as a product of prime powers
-- statement:
--   For every natural number $n$, Landau's function $g(n)$ — the largest order of a permutation of an $n$-element set — is a product of prime powers whose sum is at most $n$. More precisely, there is a finite set $t$ of prime powers (each of the form $p^k$ with $p$ prime and $k \geq 1$) such that $\sum_{q \in t} q \leq n$ and $\prod_{q \in t} q = g(n)$.
--
--   This is the sup/max bookkeeping half of the identification of Landau's function with a knapsack optimum over prime-power families: the maximum order is attained, and the attaining permutation's order decomposes into prime powers. The converse direction — that every prime-power family with sum at most $n$ has product at most $g(n)$ — is a separate statement.

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Definitions.Def_LandauExplore_landauLocal

open Finset

namespace LandauExplore
theorem landau_primePow_decomp (n : ℕ) :
    ∃ t : Finset ℕ, (∀ q ∈ t, ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ q = p ^ k)
      ∧ ∑ q ∈ t, q ≤ n ∧ ∏ q ∈ t, q = landauLocal n := by sorry
end LandauExplore
