-- Prove2me | Theorems.Thm_LCAntiConc_lemma_C_3
-- name    : LCAntiConc.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:20.130979+00:00
-- url     : https://prove2.me/theorems/2cf6ec89-92ae-44fe-b030-60aa3fe6703d
-- title:
--   Lemma C.3 — finite polynomial envelope $P(t)^2\le2A_P^2\sum_{j\le D}(12ct)^{2j}/(2j/k)!$
-- statement:
--   Let $k\in\{1,2\}$ and $c>0$, and let $P\in\mathbb R[t]$ have degree at most $D$ and satisfy $|P(t)|\le A_Pe^{|ct|^k}$ for all real $t$. Then for all real $t$
--
--   $$P(t)^2\le2A_P^2\sum_{j=0}^{D}\frac{(12ct)^{2j}}{(2j/k)!},\tag{C.5}$$
--
--   and the difference of the two sides is a sum of squares of univariate polynomials.
--
--   The lemma turns a pointwise exponential envelope for a polynomial into a polynomial sum-of-squares envelope, which is how the derivative bounds of Lemma 4.11 enter the certificates of Lemmas 4.12–4.13.
--
--   Differences from the source: none.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma C.3, (C.5), p.49 (PDF p.51)

import Mathlib

namespace LCAntiConc

open Polynomial

/-- **Lemma C.3** (Finite polynomial envelope). Let `k ∈ {1, 2}` and `c > 0`, and let `P ∈ ℝ[t]`
have degree at most `D` and satisfy `|P(t)| ≤ A_P e^{|ct|^k}` for all real `t`. Then
`P(t)² ≤ 2A_P² ∑_{j=0}^{D} (12ct)^{2j} / (2j/k)!` (C.5), and the difference is a sum of squares
of univariate polynomials.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma C.3, p.49 (PDF p.51).

**Formalization Note** The right-hand side of (C.5) is the polynomial `S`; the natural-number
quotient `2j/k` is exact for `k ∈ {1, 2}`. Both clauses are stated. -/
theorem lemma_C_3 (k : ℕ) (hk : k = 1 ∨ k = 2) (c : ℝ) (hc : 0 < c) (D : ℕ) (A : ℝ)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ D)
    (henv : ∀ t : ℝ, |P.eval t| ≤ A * Real.exp (|c * t| ^ k)) :
    (∀ t : ℝ, (P.eval t) ^ 2 ≤
        (C (2 * A ^ 2) * ∑ j ∈ Finset.range (D + 1),
          C ((12 * c) ^ (2 * j) / ((2 * j / k).factorial : ℝ)) * X ^ (2 * j)).eval t) ∧
      IsSumSq (C (2 * A ^ 2) * ∑ j ∈ Finset.range (D + 1),
          C ((12 * c) ^ (2 * j) / ((2 * j / k).factorial : ℝ)) * X ^ (2 * j) - P ^ 2) := by sorry

end LCAntiConc
