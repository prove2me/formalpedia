-- Prove2me | Theorems.Thm_IntMul_HvdH_kronecker_unique
-- name    : IntMul.HvdH.kronecker_unique
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:17:34.318996+00:00
-- url     : https://prove2.me/theorems/167f6940-265b-435d-a5e7-6f4b690cc199
-- title:
--   Uniqueness of balanced base-$B$ expansions (Kronecker unpacking)
-- statement:
--   Let $B$ be an integer and let $c_0,\dots,c_{n-1}$ and $c'_0,\dots,c'_{n-1}$ be integers with $2|c_i|<B$ and $2|c'_i|<B$. If
--   $$\sum_{i<n}c_iB^i=\sum_{i<n}c'_iB^i,$$
--   then $c_i=c'_i$ for all $i<n$. So a polynomial with integer coefficients of absolute value below $B/2$ is determined by its value at $B$. This justifies the unpacking step (3) of Kronecker substitution in Lemma 2.5 of Harvey–van der Hoeven, where $B=2^{3p}$ and the coefficients are below $r\,2^{2p}<2^{3p-1}$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.5, Lemma 2.5 (Kronecker substitution)

import Mathlib

namespace IntMul.HvdH
theorem kronecker_unique (B : ℤ) (n : ℕ) (c c' : ℕ → ℤ) (hc : ∀ i, 2 * |c i| < B)
    (hc' : ∀ i, 2 * |c' i| < B)
    (h : ∑ i ∈ Finset.range n, c i * B ^ i = ∑ i ∈ Finset.range n, c' i * B ^ i) :
    ∀ i < n, c i = c' i := by sorry
end IntMul.HvdH
