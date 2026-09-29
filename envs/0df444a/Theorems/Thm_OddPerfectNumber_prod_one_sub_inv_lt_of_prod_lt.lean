-- Prove2me | Theorems.Thm_OddPerfectNumber_prod_one_sub_inv_lt_of_prod_lt
-- name    : OddPerfectNumber.prod_one_sub_inv_lt_of_prod_lt
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T06:52:38.746207+00:00
-- url     : https://prove2.me/theorems/11e03764-c4f5-4338-8a48-27ca8d324016
-- title:
--   Strict majorization inequality for $\prod (1-1/x_i)$ (Nielsen, Lemma 1.2)
-- statement:
--   **Strict form of the majorization inequality for products $\prod (1 - 1/x_i)$.**
--
--   Let $n \ge 1$ and let $x_0,\dots,x_{n-1}$ and $y_0,\dots,y_{n-1}$ be real numbers greater than $1$, with $y$ non-decreasing and
--
--   $$
--   \prod_{i<m} x_i \;\le\; \prod_{i<m} y_i \qquad (0 \le m \le n).
--   $$
--
--   If moreover the full products are separated, $\prod_{i<n} x_i < \prod_{i<n} y_i$, then the conclusion is strict:
--
--   $$
--   \prod_{i<n}\Bigl(1-\frac{1}{x_i}\Bigr)\;<\;\prod_{i<n}\Bigl(1-\frac{1}{y_i}\Bigr).
--   $$
--
--   This is the form in which Nielsen's Lemma 1.2 is used: the equality case of that lemma occurs only when the two sequences coincide, so a strict inequality between the total products forces a strict inequality between the two products of $1 - 1/x_i$.
--
--   **Formalization Note.** Sequences are functions `ℕ → ℝ`; only their values on `Finset.range n` matter.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), no. 295, 2549-2567; Section 1. Author's copy: https://mathdept.byu.edu/~pace/BestBound_web.pdf . Lemma 1.2 (inequality (4) together with its equality characterisation), p. 2.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem prod_one_sub_inv_lt_of_prod_lt (n : ℕ) (x y : ℕ → ℝ) (hn : 0 < n)
    (hx : ∀ i < n, 1 < x i) (hy : ∀ i < n, 1 < y i)
    (hymono : ∀ i, i + 1 < n → y i ≤ y (i + 1))
    (hle : ∀ m ≤ n, ∏ i ∈ Finset.range m, x i ≤ ∏ i ∈ Finset.range m, y i)
    (hlt : ∏ i ∈ Finset.range n, x i < ∏ i ∈ Finset.range n, y i) :
    ∏ i ∈ Finset.range n, (1 - 1 / x i) < ∏ i ∈ Finset.range n, (1 - 1 / y i) := by
  sorry

end OddPerfectNumber
