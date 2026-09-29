-- Prove2me | Theorems.Thm_OddPerfectNumber_prod_one_sub_inv_le_of_prod_le
-- name    : OddPerfectNumber.prod_one_sub_inv_le_of_prod_le
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T06:52:36.73824+00:00
-- url     : https://prove2.me/theorems/055222d4-8d26-4443-9413-1d1fc6af504c
-- title:
--   Majorization inequality for $\prod (1-1/x_i)$ (Nielsen, Lemma 1.2)
-- statement:
--   **A majorization inequality for products of the form $\prod (1 - 1/x_i)$.**
--
--   Let $n \ge 0$ and let $x_0,\dots,x_{n-1}$ and $y_0,\dots,y_{n-1}$ be real numbers, all greater than $1$. Assume that the sequence $y$ is non-decreasing, and that every partial product of the $x$'s is dominated by the corresponding partial product of the $y$'s:
--
--   $$
--   \prod_{i<m} x_i \;\le\; \prod_{i<m} y_i \qquad (0 \le m \le n).
--   $$
--
--   Then
--
--   $$
--   \prod_{i<n}\Bigl(1-\frac{1}{x_i}\Bigr)\;\le\;\prod_{i<n}\Bigl(1-\frac{1}{y_i}\Bigr).
--   $$
--
--   In words: among sequences whose partial products are bounded below by a fixed non-decreasing sequence, the fixed sequence itself minimises $\prod (1-1/x_i)$. This is the analytic heart of the Heath-Brown-Cook-Nielsen upper bounds for odd perfect numbers: it is what allows one to replace an unknown tuple of prime powers by an explicit extremal tuple.
--
--   **Formalization Note.** Sequences are functions `ℕ → ℝ` and only their values on `Finset.range n` matter; the hypotheses are stated for indices below `n`. Nielsen's Lemma 1.2 assumes both sequences are non-decreasing and adds an equality characterisation; the monotonicity of $x$ is not needed for the inequality itself, so it is omitted here.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), no. 295, 2549-2567; Section 1. Author's copy: https://mathdept.byu.edu/~pace/BestBound_web.pdf . Lemma 1.2 (inequality (4)), p. 2.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem prod_one_sub_inv_le_of_prod_le (n : ℕ) (x y : ℕ → ℝ)
    (hx : ∀ i < n, 1 < x i) (hy : ∀ i < n, 1 < y i)
    (hymono : ∀ i, i + 1 < n → y i ≤ y (i + 1))
    (hle : ∀ m ≤ n, ∏ i ∈ Finset.range m, x i ≤ ∏ i ∈ Finset.range m, y i) :
    ∏ i ∈ Finset.range n, (1 - 1 / x i) ≤ ∏ i ∈ Finset.range n, (1 - 1 / y i) := by
  sorry

end OddPerfectNumber
