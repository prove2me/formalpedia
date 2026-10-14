-- Prove2me | Theorems.Thm_IntMul_HvdH_sum_pow_eq_zero
-- name    : IntMul.HvdH.sum_pow_eq_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:02:23.761678+00:00
-- url     : https://prove2.me/theorems/303d33bf-2a60-47dd-99bb-fd00a8d25f8e
-- title:
--   If $\omega^{2^e}=-1$ then $\omega$ is a principal $2^{e+1}$-th root of unity
-- statement:
--   Let $R$ be any commutative ring and $\omega\in R$ with $\omega^{2^e}=-1$. Then for every integer $j\ge0$ not divisible by $2^{e+1}$,
--   $$\sum_{k=0}^{2^{e+1}-1}\omega^{jk}=0 .$$
--   So $\omega$ is a principal $2^{e+1}$-th root of unity in the sense of §2.4 of Harvey–van der Hoeven, even when $R$ has zero divisors. The main example is $R=\mathbb C[y]/(y^r+1)$ with $\omega=y^{2r/n}$, $n\mid 2r$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 3.1 (Lemma 2.3, (2.1), Lemma 3.2)

import Mathlib

namespace IntMul.HvdH
theorem sum_pow_eq_zero {R : Type*} [CommRing R] (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (j : ℕ)
    (hj : ¬ 2 ^ (e + 1) ∣ j) : ∑ k ∈ Finset.range (2 ^ (e + 1)), ω ^ (j * k) = 0 := by sorry
end IntMul.HvdH
