-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_interval_van_der_corput
-- name    : OAI.ShortEgyptian.interval_van_der_corput
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:40.519362+00:00
-- url     : https://prove2.me/theorems/f93b116c-d513-45a7-ae9f-60700d5ca9b2
-- title:
--   Van der Corput's inequality for a bounded sequence supported on an integer interval
-- statement:
--   Let $p\le q$ be integers, $I=\{p,p+1,\dots,q\}$ and $M=|I|=q-p+1$. Let $a:\mathbb{Z}\to\mathbb{C}$ be supported on $I$ (that is, $a(n)=0$ for $n\notin I$) with $|a(n)|\le1$ for $n\in I$. Let $L\ge1$ be an integer and $C\ge0$ a real number, and suppose that all correlations of $a$ with shifts $1\le h<L$ are bounded by $C$:
--   $$
--   \Bigl|\sum_{n\in I}a(n+h)\,\overline{a(n)}\Bigr|\le C\qquad\text{for all integers }1\le h<L.
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n\in I}a(n)\Bigr|^2\le\frac{M+L}{L}\,M+(M+L)\,C .
--   $$
--
--   This is van der Corput's inequality (Weyl differencing): a bound for the sum follows from bounds for its shifted autocorrelations, at the cost of a square. The first term, of order $M^2/L$ when $L\le M$, is the price of averaging over $L$ shifts. Iterating the inequality reduces exponential sums with a polynomial-like phase to sums with differenced phases.
--
--   **Formalization Note** $I$ is `Finset.Icc p q` in the integers, complex conjugation is `starRingEnd ℂ`, and $M$ is the cardinality of $I$ cast to a real number. Because $a$ vanishes outside $I$, the terms with $n+h>q$ in the correlation sums are zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IntervalDifferencing.lean#L117-L173

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing

open OAI OAI.ShortEgyptian
universe uι uκ uM
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.interval_van_der_corput (a : ℤ → ℂ) (p q : ℤ) (hpq : p ≤ q)
    (L : ℕ) (hL : 1 ≤ L) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : ∀ n, n ∉ Icc p q → a n = 0)
    (hnorm : ∀ n ∈ Icc p q, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 1 ≤ h → h < L →
      ‖∑ n ∈ Icc p q, a (n + h) * (starRingEnd ℂ) (a n)‖ ≤ C) :
    ‖∑ n ∈ Icc p q, a n‖ ^ 2 ≤
      (((Icc p q).card : ℝ) + L) / L * (Icc p q).card +
      (((Icc p q).card : ℝ) + L) * C := by sorry
