-- Prove2me | Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
-- name    : NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/282c6675-36b9-5408-b9ef-e9be9f1114e2
-- title:
--   Primes with norm ≡ 1 (mod m) split completely in K(ζ_m)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $m$ be a nonzero natural number, and assume $L$ is an $m$-th cyclotomic extension of $K$ in the sense of Mathlib's `IsCyclotomicExtension {m} K L`, i.e. $L$ is generated over $K$ by the primitive $m$-th roots of unity and such a root exists in $L$. Let $v$ be a maximal ideal of the ring of integers $\mathcal{O}_K$ whose absolute norm $N(v) = \lvert \mathcal{O}_K / v\rvert$ is coprime to $m$ and satisfies $N(v) \equiv 1$ in $\mathbb{Z}/m\mathbb{Z}$. Then two conclusions hold simultaneously. First, the set of primes of $\mathcal{O}_L$ lying over $v$ — that is, the prime ideals $w$ of $\mathcal{O}_L$ with $w \cap \mathcal{O}_K = v$, in the sense of `Ideal.primesOver` — has cardinality (as a set-theoretic cardinality of a set, via `Set.ncard`) equal to $\operatorname{finrank}_K L = [L:K]$. Second, every prime $w$ of $\mathcal{O}_L$ lying over $v$ has absolute norm equal to that of $v$, i.e. $N(w) = N(v)$, so the residue degree of $w$ over $v$ is $1$.
--
--   This is the splitting half of the decomposition law for cyclotomic extensions: a prime of $K$ whose norm is prime to $m$ and congruent to $1$ modulo $m$ splits completely in $K(\zeta_m)$, with all residue degrees equal to one (the full law gives residue degree the order of $N(v)$ in $(\mathbb{Z}/m\mathbb{Z})^\times$). It is used in the analytic estimates on sums $\sum_w N(w)^{-s}$ over primes of a cyclotomic extension, namely in [`NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension) and [`NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension`](thm.html#NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
    (h1 : (Ideal.absNorm v : ZMod m) = 1) :
    (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by sorry
