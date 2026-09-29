-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_lemma_1_4
-- name    : OddPerfectNumber.nielsen_lemma_1_4
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-08T06:52:40.021279+00:00
-- url     : https://prove2.me/theorems/729a44b8-273f-45f8-8689-502334e3c769
-- title:
--   Nielsen's arithmetic lemma: $a\prod x_i \le (a+1)^{2^r}-(a+1)^{2^{r-1}}$
-- statement:
--   **Nielsen's key arithmetic lemma.**
--
--   Let $r, a, b$ be positive integers and let $1 < x_1 \le x_2 \le \dots \le x_r$ be integers such that
--
--   $$
--   \prod_{i=1}^{r}\Bigl(1-\frac{1}{x_i}\Bigr)\;\le\;\frac{a}{b}\;<\;\prod_{i=1}^{r-1}\Bigl(1-\frac{1}{x_i}\Bigr).
--   $$
--
--   Then
--
--   $$
--   a\prod_{i=1}^{r}x_i\;\le\;(a+1)^{2^{r}}-(a+1)^{2^{r-1}}.
--   $$
--
--   The bound is best possible: equality holds for $b = a+1$ and the extremal tuple $x_i = (a+1)^{2^{i-1}}+1$ for $i<r$, $x_r = (a+1)^{2^{r-1}}$.
--
--   This lemma is the engine of every known upper bound for odd perfect numbers. Given a "sandwich" condition on a product of terms $1 - 1/x_i$ around a rational number $a/b$, it converts the analytic information into a doubly exponential upper bound on the product of the $x_i$ themselves. It strengthens Lemma 1 of Nielsen's 2003 paper (which gave the weaker bound $a\prod x_i < (a+1)^{2^r}$) both by allowing repetitions among the $x_i$ and by subtracting the term $(a+1)^{2^{r-1}}$.
--
--   **Formalization Note.** The tuple is given by a function `x : ℕ → ℕ` and only its values on indices `< r` are used; monotonicity is stated stepwise. The final subtraction is truncated subtraction on `ℕ`, which is harmless since $(a+1)^{2^{r-1}} \le (a+1)^{2^{r}}$. The two hypotheses on $a/b$ are stated over `ℝ`.
-- source:
--   P. P. Nielsen, Odd perfect numbers, Diophantine equations, and upper bounds, Math. Comp. 84 (2015), no. 295, 2549-2567; Section 1. Author's copy: https://mathdept.byu.edu/~pace/BestBound_web.pdf . Lemma 1.4, pp. 3-4. Strengthens P. P. Nielsen, An upper bound for odd perfect numbers, INTEGERS 3 (2003), #A14, Lemma 1.

import Mathlib
open Finset

namespace OddPerfectNumber

theorem nielsen_lemma_1_4 (r a b : ℕ) (x : ℕ → ℕ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hx1 : ∀ i < r, 1 < x i) (hxmono : ∀ i, i + 1 < r → x i ≤ x (i + 1))
    (h1 : ∏ i ∈ Finset.range r, (1 - 1 / (x i : ℝ)) ≤ (a : ℝ) / b)
    (h2 : (a : ℝ) / b < ∏ i ∈ Finset.range (r - 1), (1 - 1 / (x i : ℝ))) :
    a * ∏ i ∈ Finset.range r, x i ≤ (a + 1) ^ 2 ^ r - (a + 1) ^ 2 ^ (r - 1) := by
  sorry

end OddPerfectNumber
