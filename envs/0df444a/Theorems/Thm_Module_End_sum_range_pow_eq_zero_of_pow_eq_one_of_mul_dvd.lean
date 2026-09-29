-- Prove2me | Theorems.Thm_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd
-- name    : Module.End.sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/e21962ce-5039-5388-a3fd-8e9f8c296e11
-- title:
--   Geometric sums of a finite-order endomorphism vanish in characteristic p
-- statement:
--   Let $R$ be a commutative ring, $V$ an additive commutative group equipped with an $R$-module structure, and let $p$ be a natural number such that $R$ has characteristic $p$ (in the `CharP` sense, so that $p$ generates the kernel of $\mathbb{Z}\to R$; no primality is required, and $p=0$ is permitted). Let $T$ be an $R$-linear endomorphism of $V$, and let $d, n$ be natural numbers. Assume $T^{d} = 1$, the identity of the endomorphism ring, and assume $p\,d \mid n$. The conclusion is that the partial geometric sum $\sum_{i \in \{0,\dots,n-1\}} T^{i}$ is the zero endomorphism of $V$. Equivalently: if the order of $T$ divides $d$ and the number of terms is a multiple of $p\,d$, the sum of the first $n$ powers of $T$ vanishes. For $p = 0$ the divisibility $p\,d \mid n$ forces $n = 0$ and the assertion is the empty sum.
--
--   This is the statement that the norm element of a cyclic group of order divisible by $p$ times the order of a generator's image acts as zero on a module over a ring of characteristic $p$. It is used in the computation bounding invariants plus the dual twist against the dimension of continuous classes, [`groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses`](thm.html#groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses), where divisibility conditions on orders in a local Galois group are converted into vanishing of partial sums of powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (p : ℕ) [CharP R p] (T : Module.End R V) {d n : ℕ} (hd : T ^ d = 1) (hdn : p * d ∣ n) :
    ∑ i ∈ Finset.range n, T ^ i = 0 := by sorry
