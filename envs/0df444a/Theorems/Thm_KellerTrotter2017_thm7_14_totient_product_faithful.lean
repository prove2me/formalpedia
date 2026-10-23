-- Prove2me | Theorems.Thm_KellerTrotter2017_thm7_14_totient_product_faithful
-- name    : KellerTrotter2017.thm7_14_totient_product_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:54.307064+00:00
-- url     : https://prove2.me/theorems/9b494cc3-490d-427d-9ad6-a7eb8b5b1da4
-- title:
--   Theorem 7.14 — $\varphi(n) = n\prod_{p \mid n}(p-1)/p$
-- statement:
--   Let $n \ge 2$ and let $p_1, \dots, p_m$ be the distinct prime factors of $n$. Let $\varphi(n)$ be the number of integers in $\{1, \dots, n\}$ that are relatively prime to $n$. Then
--
--   $$\varphi(n) = n \prod_{i=1}^{m} \frac{p_i - 1}{p_i}.$$
--
--   This is Theorem 7.14 of Keller and Trotter, *Applied Combinatorics*, the number-theoretic application of Inclusion–Exclusion in Chapter 7.
--
--   **Formalization Note** $\varphi$ is Mathlib's Euler totient function, and the identity is stated in the rational numbers $\mathbb Q$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 150, Theorem 7.14

import Mathlib

theorem KellerTrotter2017.thm7_14_totient_product_faithful (n : ℕ) (hn : 2 ≤ n) :
    (Nat.totient n : ℚ) = n * ∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / p) := by sorry
