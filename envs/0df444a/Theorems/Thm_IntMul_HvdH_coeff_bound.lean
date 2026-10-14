-- Prove2me | Theorems.Thm_IntMul_HvdH_coeff_bound
-- name    : IntMul.HvdH.coeff_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:17:28.904202+00:00
-- url     : https://prove2.me/theorems/172a2ce5-1dbb-4715-8b3a-92a3bbc61367
-- title:
--   Coefficient bound for (nega)cyclic products: $|\sum_k \pm a_kb_{j-k}|\le rM^2$
-- statement:
--   Let $r\ge1$ and let $a,b:\mathbb Z/r\to\mathbb Z$ have entries of absolute value at most $M$. For any signs (more generally any weights $s_{k,j}$ with $|s_{k,j}|\le1$) and any $j$,
--   $$\Big|\sum_{k}a_k\,b_{j-k}\,s_{k,j}\Big|\le rM^2 .$$
--   With $s$ the negacyclic signs this bounds the coefficients of a product in $\mathbb Z[y]/(y^r+1)$, as in the remark before Lemma 2.5 of Harvey–van der Hoeven ($\|uv\|\le r\|u\|\|v\|$).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.5, Lemma 2.5 (Kronecker substitution)

import Mathlib

namespace IntMul.HvdH
theorem coeff_bound {r : ℕ} [NeZero r] (a b : ZMod r → ℤ) (M : ℤ) (ha : ∀ k, |a k| ≤ M)
    (hb : ∀ k, |b k| ≤ M) (s : ZMod r → ZMod r → ℤ) (hs : ∀ k j, |s k j| ≤ 1) (j : ZMod r) :
    |∑ k, a k * b (j - k) * s k j| ≤ r * M ^ 2 := by sorry
end IntMul.HvdH
