-- Prove2me | Theorems.Thm_Nat_eq_of_forall_dvd_sum_divisors_eq
-- name    : Nat.eq_of_forall_dvd_sum_divisors_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/2aee80da-7c1d-50b6-9e90-d194286036f5
-- title:
--   Divisor sums over all divisors of n determine the summands
-- statement:
--   Let $n$ be a natural number with $0 < n$, and let $m, m' \colon \mathbb{N} \to \mathbb{N}$ be two arithmetic functions with natural-number values. Assume that for every natural number $e$ dividing $n$ the two divisor sums agree, $\sum_{d \in \mathrm{divisors}(e)} m(d) = \sum_{d \in \mathrm{divisors}(e)} m'(d)$, where $\mathrm{divisors}(e)$ is the finite set of positive divisors of $e$ (empty when $e = 0$, though this case does not occur for divisors of a positive $n$). The conclusion is that $m$ and $m'$ agree pointwise on all divisors of $n$: for every $d$ with $d \mid n$ one has $m(d) = m'(d)$. No assumption of multiplicativity is made on $m$ or $m'$, and the hypothesis and conclusion are both restricted to the divisors of $n$; nothing is asserted about the values of $m$ and $m'$ at natural numbers not dividing $n$.
--
--   This is the triangular (Möbius) inversion over the divisor lattice of $n$, in the elementary form that needs no Möbius function: the partial sums over divisors of each $e \mid n$ determine the individual terms. It is used by [`Representation.exists_linearEquiv_of_finrank_invariants_eq`](thm.html#Representation.exists_linearEquiv_of_finrank_invariants_eq) to recover the multiplicities of the cyclotomic constituents of a module over a cyclic group from the dimensions of fixed subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Nat_eq_of_forall_dvd_sum_divisors_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum

theorem Nat.eq_of_forall_dvd_sum_divisors_eq {n : ℕ} (hn : 0 < n) (m m' : ℕ → ℕ)
    (h : ∀ e, e ∣ n → ∑ d ∈ e.divisors, m d = ∑ d ∈ e.divisors, m' d) :
    ∀ d, d ∣ n → m d = m' d := by sorry
