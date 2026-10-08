-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_bounded_prime_triple_estimate
-- name    : OAI.TwoPointCorrelations.halasz_bounded_prime_triple_estimate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:22.1568+00:00
-- url     : https://prove2.me/theorems/3d644848-8082-433a-a920-bfed85eaa587
-- title:
--   A Halász-type bound for the triple convolution of two prime polynomials with a smooth-supported function
-- statement:
--   There are $C>0$ and $B\ge2$ such that the following holds. Let $f:\mathbb N\to\mathbb C$ with $|f(n)|\le1$ for $n\ge1$, $N\in\mathbb N$, and $f_N=$ `halaszSmoothFunction f N` (equal to $f(n)$ when $n$ is $(N+1)$-smooth, i.e. all prime factors are at most $N$, and $0$ otherwise). Let $x>0$ not an integer, $m\ge1$ an integer with $m\le x$, $T\ge B$, $A,W,R\ge0$. Let $P$ be a finite set of primes $p\ge T^2$, $Q$ a finite set of primes, and $a,b:\mathbb N\to\mathbb C$ with $|a(p)|\le R$ on $P$ and $|b(q)|\le1$ on $Q$. Suppose $|L(f_N,1+it)|\le A$ for $|t|\le T$ and $|L(f_N,1+it)|\le W$ for all real $t$, where $L(\cdot,s)$ is the Dirichlet series (Mathlib's `LSeries`). Then, with $\alpha(n)=\mathbf 1_P(n)\log n\,a(n)$, $\beta(n)=\mathbf 1_Q(n)\log n\,b(n)$ and $\ast$ Dirichlet convolution,
--
--   $$\Big|\sum_{1\le n\le x}(\alpha*\beta*f_N)(n)\Big|\le CxA\Big(\sum_{p\in P}|a(p)|^2\tfrac{\log p}{p}\Big)^{1/2}\Big(\sum_{q\in Q}|b(q)|^2\tfrac{\log q}{q}\Big)^{1/2}+\frac{40x\big(R\sum_{P}\frac{\log p}{p}\big)\big(\sum_{Q}\frac{\log q}{q}\big)W}{(m/x)\,T}+R\log^2(x+m)\,m.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_bounded_prime_triple_estimate`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex
open MeasureTheory
open _root_.Erdos970 (VerticalIntegral VerticalIntegral')
open scoped Classical
open scoped LSeries.notation

theorem halasz_bounded_prime_triple_estimate : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), OneBounded f →
    ∀ (N : ℕ) (x T A W R : ℝ) (m : ℕ), 0 < x → 0 < m → (m : ℝ) ≤ x →
      (∀ n : ℕ, x ≠ (n : ℝ)) → B ≤ T → 0 ≤ A → 0 ≤ W → 0 ≤ R →
    ∀ (P Q : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) →
      (∀ q ∈ Q, q.Prime) → ∀ a b : ℕ → ℂ,
      (∀ p ∈ P, ‖a p‖ ≤ R) → (∀ q ∈ Q, ‖b q‖ ≤ 1) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
    ‖∑ n ∈ Icc 1 ⌊x⌋₊,
      (halaszFiniteCoefficient P (fun p => (Real.log (p : ℝ) : ℂ) * a p) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * b q) ⍟
          halaszSmoothFunction f N)) n‖ ≤
      (C * x * A) *
        (Real.sqrt (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) *
          Real.sqrt (∑ q ∈ Q, ‖b q‖ ^ 2 * (Real.log (q : ℝ) / q))) +
      40 * x * (R * ∑ p ∈ P, Real.log (p : ℝ) / p) *
        (∑ q ∈ Q, Real.log (q : ℝ) / q) * W / ((m / x) * T) +
      R * Real.log (x + m) ^ 2 * m := by
  sorry

end OAI.TwoPointCorrelations
