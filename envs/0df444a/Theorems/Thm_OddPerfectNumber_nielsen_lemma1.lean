-- Prove2me | Theorems.Thm_OddPerfectNumber_nielsen_lemma1
-- name    : OddPerfectNumber.nielsen_lemma1
-- status  : Proved
-- author  : @curiyu
-- created : 2026-09-08T04:00:34.378984+00:00
-- url     : https://prove2.me/theorems/357e25cc-6101-4d04-85c4-ec9218d08945
-- title:
--   Nielsen Lemma 1: product estimate $a\\prod x_i < (a+1)^{2^r}$
-- statement:
--   This is Lemma 1 of Nielsen 2003 (Section 2), the combinatorial engine behind the odd-perfect upper bound.
--
--   Let $r, a, b$ be positive integers and let $1 < x_1 < \dots < x_r$ be integers satisfying
--   $$
--   \prod_{i=1}^{r}\left(1-\frac{1}{x_i}\right) \le \frac{a}{b} < \prod_{i=1}^{r-1}\left(1-\frac{1}{x_i}\right).
--   $$
--   Then
--   $$
--   a\prod_{i=1}^{r} x_i < (a+1)^{2^{r}}.
--   $$
--   The estimate is used twice in the paper: directly for Proposition 1, and in the form $\Pi(S) < (B(r,a)a)^{2^{r}-1}$ for the two prime-set extensions (inequalities (1) and (4)) in the proof of Theorem 1. The published proof is by induction on $r$ following Cook, closing with Cook's Lemma 2.
--
--   **Formalization Note** The sequence is $0$-indexed in Lean ($x : \mathbb{N} \to \mathbb{N}$ with $x_i$ for $i < r$), products are over `Finset.range`, and the inequalities are stated over $\mathbb{Q}$ with explicit casts.
-- source:
--   P. P. Nielsen, An upper bound for odd perfect numbers, INTEGERS 3 (2003), #A14, Section 2, Lemma 1, https://emis.muni.cz/journals/INTEGERS/papers/d14/d14.pdf

import Mathlib
open BigOperators Finset

namespace OddPerfectNumber

theorem nielsen_lemma1 (r a b : ℕ) (x : ℕ → ℕ) (ha : 0 < a) (hb : 0 < b)
    (hx1 : ∀ i, i < r → 1 < x i)
    (hxmono : ∀ i j, i < j → j < r → x i < x j)
    (hstar : (∏ i ∈ Finset.range r, (1 - 1 / ((x i : ℕ) : ℚ))) ≤ ((a : ℕ) : ℚ) / ((b : ℕ) : ℚ) ∧
      ((a : ℕ) : ℚ) / ((b : ℕ) : ℚ) < ∏ i ∈ Finset.range (r - 1), (1 - 1 / ((x i : ℕ) : ℚ))) :
    ((a : ℕ) : ℚ) * ∏ i ∈ Finset.range r, (((x i : ℕ) : ℚ)) < (((a : ℕ) : ℚ) + 1) ^ (2 ^ r) := by
  sorry

end OddPerfectNumber
